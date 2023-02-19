# Bosque Language List Standard Library
The `List<T>` collection in Bosque is an `Nat` indexed ordered sequence of elements. It is implemented using a persistent tree implementation so all operations (including insert) are log complexity. This implementation choice minimizes performance variance (e.g. no need to resize arrays) and allows for efficient operations on sub-ranges of the list. 

As Bosque does not have an iteration operator (such as for or while) the `List<T>` type provides a rich set of methods for processing lists. 

[TODO] interesting compiler and runtime issues to discuss here.

- List Type
- List Global Functions
- List Member Functions
- List Member Methods
    1. size/empty
    2. get/front/back
    3. allOf/noneOf/someOf
    4. find
    5. findIndexOf
    6. filter/filterType
    7. castType
    8. map/project
    9. append/prepend
    10. pushBack/pushFront
    11. popBack/popFront
    12. set
    13. insert/remove
    14. reduce

# List Type
# List Global Functions
# List Member Functions

# List Member Methods

## size/empty
The `size` and `empty` operators return the number of elements in the list and whether the list is empty respectively.

```none
let l1 = List<Nat>{};
l1.size() //0
l1.empty() //true

let l2 = List<Nat>{1n, 2n, 3n};
l2.size() //3
l2.empty() //false
```