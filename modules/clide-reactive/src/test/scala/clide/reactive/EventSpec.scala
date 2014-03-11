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

class EventProps extends JUnitSuite with Checkers {
  implicit val scheduler = BlockingScheduler
  
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
  
  @Test
  def testToSeq() {
    check { (a: EventSeq) =>
      Await.result(a.event.toSeq.map(_ == a.seq), 5 seconds)
    }
  }
  
  @Test
  def testMap() {
    check { (a: EventSeq) =>
      Await.result(for {
        mapEvent <- a.event.map(_ * 2).toSeq
      } yield mapEvent == a.seq.map(_ * 2), 5 seconds)
    } 
  }
  
  @Test
  def testZip() {
    check { (a: EventSeq, b: EventSeq) => 
      Await.result(for {
        zipEvent <- (a.event zip b.event).toSeq        
      } yield zipEvent == (a.seq zip b.seq), 5 seconds)
    } 
  }
  
  @Test
  def testFind() {
    check { (a: EventSeq) =>  
      Await.result(for {
        elem <- a.event.find(_ > 7)
      } yield elem == a.seq.find(_ > 7), 5 seconds)
    }
  }
  
  @Test
  def testTake {
    check { (a: EventSeq, b: Int) =>
      Await.result(a.event.take(b).toSeq.map(_ == a.seq.take(b)),5 seconds)      
    }
  }
  
  @Test
  def testDrop {
    check { (a: EventSeq, b: Int) =>
      Await.result(a.event.drop(b).toSeq.map(_ == a.seq.drop(b)), 5 seconds)
    }
  }
  
  @Test
  def testTakeWhile {
    check { (a: EventSeq) =>
      Await.result(a.event.takeWhile(_ < 7).toSeq.map{ s =>         
        s == a.seq.takeWhile(_ < 7) },5 seconds)      
    }
  }
  
  @Test
  def testDropWhile {
    check { (a: EventSeq) =>
      Await.result(a.event.dropWhile(_ < 7).toSeq.map(_ == a.seq.dropWhile(_ < 7)), 5 seconds)
    }
  }  
  
  @Test
  def testSpan {
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
  
  @Test
  def testPartition {
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
  
  @Test
  def testTimestampedMonotonicity {
    check { (a: EventSeq) =>
      Await.result(a.event.timestamped.toSeq.map(ts => ts == ts.sortBy(_._2)), 5 seconds)
    }
  }
  
  @Test
  def testMerge {
    check { (a: EventSeq, b: EventSeq) =>      
      Await.result(a.event.timestamped.merge(b.event.timestamped).toSeq.map(ts => ts == ts.sortBy(_._2)), 5 seconds)      
    }
    check { (a: EventSeq, b: EventSeq) =>
      Await.result(a.event.merge(b.event).toSeq.map(m => m.sorted == (a.seq ++ b.seq).sorted), 5 seconds)
    }
  }
  
  @Test
  def test_++ {
    check { (a: EventSeq, b: EventSeq) =>
      Await.result((a.event ++ b.event).toSeq.map(_ == a.seq ++ b.seq), 10 seconds)
    }
  }
      
  @Test
  def testVarying {
    def varyingSeq(seq: Seq[Int]) =
      seq.take(1) ++ seq.zip(seq.drop(1)).collect { case (a,b) if a != b => b }
    check { (a: EventSeq) =>
      Await.result(a.event.varying.toSeq.map(_ == varyingSeq(a.seq)), 5 seconds)
    }
  }
}