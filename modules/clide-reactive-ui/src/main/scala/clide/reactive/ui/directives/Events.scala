package clide.reactive.ui.directives

import org.scalajs.dom._

trait Events {
  object on {
    def click(elem: HTMLElement, handler: => Unit) =
      elem.addEventListener("click", (e: Event) => handler)
    def submit(elem: HTMLElement, handler: => Unit) =
      elem.addEventListener("submit", (e: Event) => { e.preventDefault(); handler })
    def input(elem: HTMLElement, handler: => Unit) =
      elem.addEventListener("input", (e: Event) => handler)
    def toggle(elem: HTMLInputElement, handler: Boolean => Unit) =
      elem.addEventListener("change", (e: Event) => { handler(elem.checked) })
  }  
}