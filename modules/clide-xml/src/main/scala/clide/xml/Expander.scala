package clide.xml

import scala.reflect.macros.Context
import javax.xml.parsers.SAXParserFactory
import java.io.InputStream
import scala.collection.mutable.Buffer
import javax.xml.XMLConstants

object Expander {
  def expand(c: Context)(positionProvider: PositionProvider[c.type], source: InputStream): c.Expr[Any] = {
    import org.xml.sax._
    import org.xml.sax.helpers.DefaultHandler
    import c.universe._
    
    val code = Buffer.empty[Tree]
    
    object handler extends DefaultHandler {
      private var locator: Locator = null
      
      override def setDocumentLocator(locator: Locator) {
        this.locator = locator
      }
      
      @throws[SAXException]
      override def startElement(uri: String, localName: String, qName: String, attrs: Attributes) {
        
      }
      
      @throws[SAXException]
      override def endElement(uri: String, localName: String, qName: String) {
        
      }
      
      @throws[SAXException]
      override def error(e: SAXParseException) {
        
      }
      
      @throws[SAXException]
      override def fatalError(e: SAXParseException) {
        
      }
    }

    val factory = SAXParserFactory.newInstance()
    factory.setValidating(true)
    factory.setNamespaceAware(false)

    val parser = factory.newSAXParser()

    parser.parse(source, handler)
    
    c.Expr(Block(code:_*))
  }
}