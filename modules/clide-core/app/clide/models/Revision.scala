package clide.models

import clide.collaboration.Operation

case class Revision(file: Long, id: Long, op: Operation)

