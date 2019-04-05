

like in a oo language, we have projection and application

* our context is layered, for example, each `let` expression introduce a layer

* names is defined by `def` expressions, names cannot be redefined in the same layer

* import will import more names in this layer
    * import from a module
    * import a object will bring all projections of it into the layer
    * importing a name with the same type will mark it has ambiguous
    * ...



--------------


problem with sum of product

1. path constructor cannot write ... : isSet anymore
