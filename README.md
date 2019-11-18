# mlang

[![Join the chat at https://gitter.im/mlang-discuess/community](https://badges.gitter.im/mlang-discuess/community.svg)](https://gitter.im/mlang-discuess/community?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge) 
[![CircleCI](https://circleci.com/gh/molikto/mlang.svg?style=svg)](https://circleci.com/gh/molikto/mlang) 

A cubical type theory implementation with implicit arguments, structural record and sum types and more. see roadmap section for details.

see `library` and `tests` folder for sample code.

+ [Status](STATUS.md)
+ [Build & Run & Debug & Editor setup & Internals](HACKING.md)
+ [Roadmap](ROADMAP.md)

## help wanted

here are some issues that are easy to do, and they are a good way to familiarize yourself with the project, they are marked with `good first issue` in issues list, and in the code, search for `[issue 123]` where `123` is the issue number will lead you to where need to be modified.

if you need more background on a issue, plz go to gitter and ask.
    
there are other kind of TODOs in the project, they are `LATER`, `TODO`, and `FIXME`, use IntelliJ IDEA to browse them.

the one marked `FIXME` in code is important problems needs expert to figure out.


### pretty print

(ice1000, can you do this?)

The current goal of pretty print is to make it easier to debug the elaborated core term, and to present faithfully the elaborated term, they are different with concrete term in various ways:

* various notation is elaborated to different form. like `nat.zero` syntax is elaborated to `construct(0)`
  (introduction rule for sum type, where 0 means the first constructor)
* meta is elaborated
* there is no `define what(a: A, b: B): C = ??/` telescope, where `a` and `b` is in both type and term.
* more type is present in core term (see `core.type_annotation` annotation)

so some improvements:

* syntax
    * makes reference use same identifier with concrete term, instead of randomly generated term
    * makes sum type construct use name of the field instead of index
    * make the syntax more like in concrete syntax (for example application syntax)
* pretty print to HTML with clear AST delimitation/boundary, layout it properly, might print it like a tree (see Lamdu project)
