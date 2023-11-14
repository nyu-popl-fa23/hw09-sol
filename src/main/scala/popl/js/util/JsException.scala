package popl.js.util

import scala.util.parsing.input._

class JsException(val msg: String, val pos: Position) extends Exception:
  override def toString: String =
    if pos != null then
      val errPos = s"${pos.line}:${pos.column}\n"
      errPos + pos.longString + "\n\n" + msg
    else msg