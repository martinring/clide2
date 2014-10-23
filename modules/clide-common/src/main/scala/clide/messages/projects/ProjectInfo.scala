package clide.messages.projects

case class ProjectInfo(
    provider: String,
    owner: String, 
    name: String, 
    public: Boolean)