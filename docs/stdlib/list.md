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

## get/front/back
The `get`, `front` and `back` operators return the element at the specified index, the first element and the last element respectively. Index out of bounds or calling `front`/`back` on an empty list will result in a runtime error.

```none
let l1 = List<Nat>{1n, 2n, 3n};
l1.get(0n) //1n
l1.get(1n) //2n
l1.get(2n) //3n

l1.front() //1n
l1.back() //3n

let l2 = List<Nat>{};
l2.get(0n) //error
l2.front() //error
l2.back() //error
```

## allOf/noneOf/someOf
Bosque provides the `allOf`, `noneOf` and `someOf` operators to test whether all, none, or some of the elements in the list satisfy a predicate. The predicate is a function that takes an element of the list and returns a `Bool`. There are 2 flavors of these methods. In one flavor the predicate is a single argument function that just takes the element. The other flavors, `allOfIdx`, `noneOfIdx`, and `someOfIdx`, the predicate is a 2 argument function that takes the element and the index of the element in the list. 

```none
let l1 = List<Nat>{1n, 2n, 3n};
l1.allOf(pred(e) => e > 0n) //true
l1.noneOf(pred(e) => e > 0n) //false

let l2 = List<Nat>{3n, 2n, 1n};
l1.someOfIdx(pred(e, i) => e > 0n && i == 1n) //true
l1.someOfIdx(pred(e, i) => e == l2.get(i)) //true

let l3 = List<Nat>{};
l3.allOf(pred(e) => e > 0n) //true
l3.noneOf(pred(e) => e > 0n) //true
l3.someOf(pred(e) => e > 0n) //false
```