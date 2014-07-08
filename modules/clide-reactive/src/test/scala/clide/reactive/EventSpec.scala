package clide.reactive

import org.scalatest.junit.JUnitSuite
import org.scalatest.prop.Checkers
import org.scalacheck.Arbitrary._
import org.scalacheck.Prop._
import org.scalacheck.Gen._
import org.scalacheck._
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.concurrent.Await
import scala.language.postfixOps
import org.junit.Test
import org.scalatest.matchers.ShouldMatchers
import java.util.Timer
import java.util.TimerTask
import org.scalatest.FunSuite

class EventProps extends FunSuite with Checkers {
  implicit val scheduler = new Scheduler {
    def now = System.currentTimeMillis()    
    def schedule[A](period: FiniteDuration)(task: => A): Cancellable = {
      val timer = new Timer
      timer.schedule(new TimerTask { def run() = task }, period.toMillis, period.toMillis)
      Cancellable(timer.cancel())
    }
    def scheduleOnce[A](delay: FiniteDuration)(task: => A): Cancellable = {
      val timer = new Timer
      timer.schedule(new TimerTask { def run() = task }, delay.toMillis)
      Cancellable(timer.cancel())
    }
  }
  
  trait EventSeq {
    def event: Event[Int]
    def seq: Seq[Int]
    override def toString = "EventSeq(" + seq.mkString(", ") + ")"
  }
  
  implicit override val generatorDrivenConfig =
    PropertyCheckConfig(
        minSize = 0, maxSize = 10,
        minSuccessful = 50, maxDiscarded = 10,
        workers = 4)
  
  def listToEvent(list: List[(Int,Int)]): Event[Int] = { 
    val (event,channel) = Event.broadcast[Int]()
    Future {
      val it = list.iterator
      while (it.hasNext) {
        val (value,duration) = it.next
        Thread.sleep(duration)
        channel.push(value)
      } 
      channel.close()
    }
    event
  }
      
  implicit val eventGen: Gen[EventSeq] = sized { size =>
    for {
      s <- resize(size, listOf(zip(choose(0, 9), choose(0, 9))))
    } yield new EventSeq {
      def event = listToEvent(s)
      def seq = s.unzip._1
    }
  }
      
  implicit val arbEvent: Arbitrary[EventSeq] = Arbitrary(eventGen)
    
  test("Event.toSeq") {
    check { (a: EventSeq) =>
      Await.result(a.event.toSeq.map(_ == a.seq), 5 seconds)
    }
  }
  
  test("Event.duplicate") {
    check { (a: EventSeq) =>
      val (e1,e2) = a.event.duplicate
      val s1 = e1.toSeq
      val s2 = e2.toSeq
      Await.result(s1, 5 seconds) == Await.result(s2, 5 seconds)
    }
  }
    
  test("Event.map") {
    check { (a: EventSeq) =>
      Await.result(for {
        mapEvent <- a.event.map(_ * 2).toSeq
      } yield mapEvent == a.seq.map(_ * 2), 5 seconds)
    } 
  }
  
  test("Event.flatMap") {
    check { (a: EventSeq) =>
      Await.result(for {
        mapEvent <- a.event.flatMap(x => Event.interval(0.01 second).map(_ * x).take(2)).toSeq
      } yield mapEvent.sorted == a.seq.flatMap(x => Seq.tabulate(2)(_ * x)).sorted, 5 seconds)
    } 
  }
  
  test("Event.filter") {
    check { (a: EventSeq, i: Int) =>
      Await.result(for {
        mapEvent <- a.event.filter(_ < i).toSeq
      } yield mapEvent == a.seq.filter(_ < i), 5 seconds)
    } 
  }  
  
  test("Event.zip") {
    check { (a: EventSeq, b: EventSeq) => 
      Await.result(for {
        zipEvent <- (a.event zip b.event).toSeq        
      } yield zipEvent == (a.seq zip b.seq), 5 seconds)
    } 
  }
  
  test("Event.find") {
    check { (a: EventSeq) =>  
      Await.result(for {
        elem <- a.event.find(_ == 7)
      } yield elem == a.seq.find(_ == 7), 5 seconds)
    }
  }
  
  test("Event.take") {
    check { (a: EventSeq, b: Int) =>
      Await.result(a.event.take(b).toSeq.map(_ == a.seq.take(b)),5 seconds)      
    }
  }
  
  test("Event.drop") {
    check { (a: EventSeq, b: Int) =>
      Await.result(a.event.drop(b).toSeq.map(_ == a.seq.drop(b)), 5 seconds)
    }
  }
  
  test("Event.takeWhile") {
    check { (a: EventSeq) =>
      Await.result(a.event.takeWhile(_ < 7).toSeq.map{ s =>         
        s == a.seq.takeWhile(_ < 7) },5 seconds)      
    }
  }
  
  test("Event.dropWhile") {
    check { (a: EventSeq) =>
      Await.result(a.event.dropWhile(_ < 7).toSeq.map(_ == a.seq.dropWhile(_ < 7)), 5 seconds)
    }
  }  
  
  test("Event.span") {
    check { (a: EventSeq) =>
      Await.result({
        val (l,r) = a.event.span(_ < 7)
        for {
          l <- l.toSeq
          r <- r.toSeq
        } yield ((l,r) == a.seq.span(_ < 7))
      }, 5 seconds)
    }
  }
  
  test("Event.completedSpan") {    
    val (e,channel) = Event.broadcast[Int]()
    channel.push(1)
    channel.push(2)
    channel.push(3)
    Thread.sleep(100)
    val (compl,rest) = e.completedSpan
    assert(compl == List(1,2,3))
    channel.push(4)
    channel.push(5)
    Thread.sleep(100)
    val (compl2,rest2) = rest.completedSpan
    assert(compl2 == List(4,5))
  }
  
  test("Event.partition") {
    check { (a: EventSeq) =>
      Await.result({
        val (l,r) = a.event.partition(_ < 5)
        for {
          l <- l.toSeq
          r <- r.toSeq
        } yield ((l,r) == a.seq.partition(_ < 5))
      }, 5 seconds)
    }
  }
  
  test("Event.scan") {
    check { (a: EventSeq) =>
      Await.result(a.event.scan(0)(_ * _).toSeq, 5 seconds) == a.seq.scan(0)(_ * _)
    }
  }
  
  test("Event.timestamped (monotonous)") {
    check { (a: EventSeq) =>
      Await.result(a.event.timestamped.toSeq.map(ts => ts == ts.sortBy(_._2)), 5 seconds)
    }
  }
  
  test("Event.merge") {
    check { (a: EventSeq, b: EventSeq) =>      
      Await.result(a.event.timestamped.merge(b.event.timestamped).toSeq.map(ts => ts == ts.sortBy(_._2)), 5 seconds)      
    }
    check { (a: EventSeq, b: EventSeq) =>
      Await.result(a.event.merge(b.event).toSeq.map(m => m.sorted == (a.seq ++ b.seq).sorted), 5 seconds)
    }
  }
  
  test("Event ++") {
    check { (a: EventSeq, b: EventSeq) =>
      Await.result((a.event ++ b.event).toSeq.map(_ == a.seq ++ b.seq), 10 seconds)
    }
  }
      
  test("Event.varying") {
    def varyingSeq(seq: Seq[Int]) =
      seq.take(1) ++ seq.zip(seq.drop(1)).collect { case (a,b) if a != b => b }
    check { (a: EventSeq) =>
      Await.result(a.event.varying.toSeq.map(_ == varyingSeq(a.seq)), 5 seconds)
    }
  }  
}