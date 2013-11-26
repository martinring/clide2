Clide2 (beta)
=====================================

*Clide2* is a cloud-based, language agnostic, collaborative development environment. *Clide* started as a web interface for the [Isabelle](http://isabelle.in.tum.de/) theorem prover but has now been extended to a general collaborative environment for the creation of arbitrary content.

Features
--------

* **Mobile** - The default front end of clide runs in the browser and utilizes state-of-the-art HTML5.

* **Collaborative** - The entire architecture is natively built around collaboration.

* **Extensible** - Clide introduces the concept of *universal collaboration*: the distinction between human and non-human collaborators is dropped.

* **Distributed** - All aspects of the development experience can be provided on different servers. Clide takes care of coordinating all those information and integrating them into a smooth user experience.


Live Demo
---------

There is a pre-release beta version live. You might just give it a spin:

> http://clide.informatik.uni-bremen.de

Installation
------------

If you consider contributing to the project, you should first set up a local instance of the clide infrastructure by following these simple steps:

1. Download a copy of the current snapshot bundle from

   > http://martin.flatmap.net/downloads/clide/clide-web-2.0-SNAPSHOT.zip

2. Unzip somewhere on your system

3. In a terminal `cd` to the path where you unzipped the package

4. start the server with `bin/clide-web`.

5. Use your browser (recommended is a current WebKit based or Internet Explorer 11) to navigate to `localhost:9000`.

You can then sign up as a new user, create projects and collaborate on files. But you will want to install additional *Assistant*-Servers in order to get semantic help and content assist functionality as you would expect from an IDE:

```
> TODO: Describe Isabelle Assistant Setup
```

Building Assistants
-------------------

The clide-core dependency can be obtained from sonatype central maven repo.

Sbt:

```
"net.flatmap" %% "clide-core" % "2.0-SNAPSHOT"
```


Maven:

```
<dependency>
  <groupId>net.flatmap</groupId>
  <artifactId>clide-core_2.10</artifactId>
  <version>2.0-SNAPSHOT</version>
</dependency>
```

License
-------

(c) copyright 2012-2013 by Martin Ring <<martin.ring@dfki.de>>

Clide2 is licensed under the LGPL v3.0 (http://www.gnu.org/copyleft/lesser.html)

THERE IS NO WARRANTY FOR THE PROGRAM, TO THE EXTENT PERMITTED BY APPLICABLE
LAW. EXCEPT WHEN OTHERWISE STATED IN WRITING THE COPYRIGHT HOLDERS AND/OR OTHER
PARTIES PROVIDE THE PROGRAM “AS IS” WITHOUT WARRANTY OF ANY KIND, EITHER
EXPRESSED OR IMPLIED, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE. THE ENTIRE RISK AS TO THE
QUALITY AND PERFORMANCE OF THE PROGRAM IS WITH YOU. SHOULD THE PROGRAM PROVE
DEFECTIVE, YOU ASSUME THE COST OF ALL NECESSARY SERVICING, REPAIR OR CORRECTION.

IN NO EVENT UNLESS REQUIRED BY APPLICABLE LAW OR AGREED TO IN WRITING WILL ANY
COPYRIGHT HOLDER, OR ANY OTHER PARTY WHO MODIFIES AND/OR CONVEYS THE PROGRAM AS
PERMITTED ABOVE, BE LIABLE TO YOU FOR DAMAGES, INCLUDING ANY GENERAL, SPECIAL,
INCIDENTAL OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OR INABILITY TO USE
THE PROGRAM (INCLUDING BUT NOT LIMITED TO LOSS OF DATA OR DATA BEING RENDERED
INACCURATE OR LOSSES SUSTAINED BY YOU OR THIRD PARTIES OR A FAILURE OF THE
PROGRAM TO OPERATE WITH ANY OTHER PROGRAMS), EVEN IF SUCH HOLDER OR OTHER PARTY
HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
