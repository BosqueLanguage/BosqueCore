# Bosque Language List Standard Library
The `List<T>` collection in Bosque is an `Nat` indexed ordered sequence of elements. It is implemented using a persistent tree implementation so all operations (including insert) are log complexity. This implementation choice minimizes performance variance (e.g. no need to resize arrays) and allows for efficient operations on sub-ranges of the list. 

As Bosque does not have an iteration operator (such as for or while) the `List<T>` type provides a rich set of methods for processing lists. 

[TODO] interesting compiler and runtime issues to discuss here.
