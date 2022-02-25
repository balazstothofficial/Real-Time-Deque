An implementation of a double-ended Queue (Deque) with dequeue and enqueue operations for both ends in *O(1)*. The complexity property is met by not having any recursive calls in these operations. If the two ends of the deque are getting unbalanced in size, a transformation is started to rebalance them. This transformation is executed with a fixed number of steps in each following enqueue- or dequeue-operation until the ends are balanced out again.

[Realtime-Deque](RealTimeDeque.thy)

Implementation of the Realtime-Deque.

The Realtime-Deque can be in the following states:

* `Empty`: No values stored. No dequeue operation possible.
* `One`: One element in the Deque.
* `Two`: Two elements in the Deque.
* `Three`: Three elements in the Deque.
* `Idle`: Deque with a left and a right end, fulfilling the following invariant:
	* 3 * size of left end >= size of right end
	* 3 * size of right end >= size of left end
	* Neither of the ends is empty
* `Transformation`: Deque which violated the invariant of the `idle` state by non-balanced dequeue and enqueue operations. The invariants during in this state are:
	* The `transformation` is not done yet. The Deque needs to be in `idle` state otherwise.
	* The `transformation` is in a valid state (Defined in [Transformation.thy](Transformation.thy))
	* The two ends of the Deque are in a size window, such that after finishing the `transformation` the invariant of the `idle` state will be met. 

The Realtime-Deque has following operations:

* `isEmpty`: Checks if a deque is in the `Empty` state
* `dequeueLeft’`: Dequeues an element on the left end and return the element and the deque without this element. If the deque is in `idle` state and the size invariant is violated either a `transformation` is started or if there are 3 or less elements left the respective states are used. On `transformation` start, six steps are executed initially. During `transformation` state four steps are executed and if it is finished the deque returns to `idle` state.
* `dequeueLeft`: Removes one element on the left end and only returns the new deque.
* `firstLeft`: Removes one element on the left end and only returns the element.
* `enqueueLeft`: Enqueues an element on the left and returns the resulting deque. Like in `dequeueLeft’` when violating the size invariant in `idle` state, a `transformation` with six initial steps is started. During `transformation` state four steps are executed and if it is finished the deque returns to `idle` state.
* `swap`: The two ends of the deque are swapped.
* `dequeueRight’`, `dequeueRight`, `firstRight`, `enqueueRight`: Same behaviour as the left-counterparts. Implemented using the left-counterparts by swapping the deque before and after the operation.
* `listLeft`, `listRight`: Get all elements of the deque in a list starting at the left or right end. They are needed for the correctness proofs.

[Deque](Deque.thy)

Specification of the expected behaviour of a deque using list abstractions. These are proven for the Realtime-Deque implementation.

[Stack](Stack.thy)

A datatype encapsulating two lists, which will be used as a base data-structure in different places. It has the operations `push`, `pop` and `first` to insert and remove elements. The function `toList` appends the two lists and is needed for the list abstraction of the deque.

[Idle](Idle.thy)

Represents the `idle` state of one Deque end. It contains a `stack` and its size as a natural number. It has the operations `push`, `pop` and `first` to insert and remove elements. The function `toList` is needed for the list abstraction of the deque.

[Transformation](Transformation.thy)

A `transformation` goes either from right to left (called `Left`), meaning that elements are transferred from the right to the left end, or from left to right (called `Right`), meaning that elements are transferred from the left to the right end. The side where the elements are transferred to contains a `small` state and the side where the elements are transferred from contains a `big` state. These states are implemented in [Small.thy](Small.thy) and [Big.thy](Big.thy).

*Functions:*

* `tick`: Executes one step of the `transformation`, while keeping the invariant.
* `remainingSteps`: Returns how many steps are left until the `transformation` is finished.
* `inSizeWindow`: Specifies if it is possible to finish the `transformation`, in such a way that the size constraints of the Idle state are met.
* `toListLeft`, `toListRight`: List abstractions.

The implementations of these functions are delegated to their respective implementation in [States.thy](States.thy), where the order of the two ends doesn’t play a role anymore. 

[States](States.thy)

`states` is a type-alias for a tuple of a `big` and a `small` state, representing the two deque ends during the `transformation` state.

*Functions:*

* `tick`: Executes one step of the `transformation`, while keeping the invariant. Delegates to the implementation in [Big.thy](Big.thy) and [Small.thy](Small.thy), except of the case where elements are transferred from the bigger end to the smaller end.
* `remainingSteps`: Returns the maximum of remaining steps of the two ends until the transformation is finished.
* `toList`, `toListSmallFirst`, `toListBigFirst`: List abstractions using the list abstractions of the two states [big](Big.thy) and [small](Small.thy) which are based on how these will look like if the transformation is finished.
* `toCurrentList`, `toCurrentListSmallFirst`, `toCurrentListBigFirst`: List abstractions using the list abstractions of the two states [big](Big.thy) and [small](Small.thy) which are based on their `current` state in the `transformation`.
* `invariant`: Based on the invariants of [small](Small.thy) and [big](Big.thy) adding the constraint that the two different list abstractions need to be the same and excludes invalid combinations of phases of the bigger and small deque end.
* `inSizeWindow’`, `inSizeWindow`: Specifies if it is possible to finish the `transformation`, in such a way that the size constraints of the `idle` state of the deque are met.

[Small](Small.thy)

The smaller end of the deque during `transformation` can be in three phases:

* `Reverse1`: Using the `tick` function the originally contained elements are reversed.
* `Reverse2`: Using the `tick` function the newly obtained elements from the bigger end are reversed on top of the ones reversed in the previous phase.
* `Common`: Specified in [Common.thy](Common.thy). Is used to reverse the elements from the two previous steps again to get them again in the original order.

Each phase contains a `current` state, which holds the original elements of the deque end. 

*Functions:*

* `push`, `pop`: Add and remove elements using the `current` state.
* `invariant`: Defines an invariant which need to be kept during the three transformation phases.
* `tick`: Executes one step of the transformation, while keeping the invariant.
* `newSize`: Returns the size, that the deque end will have after the transformation is finished.
* `size`: Minimum of `newSize` and the number of elements contained in the `current` state.
* `toList`: List abstraction of the elements which this end will contain after the transformation is finished. The first phase is not covered, since the elements, which will be transferred from the bigger deque end are not known yet.
* `toCurrentList`: List abstraction of the elements currently in this deque end.

[Big](Big.thy)

The bigger end of the deque during transformation can be in two phases:


* `Reverse`: Using the `tick` function the originally contained elements, which will be kept in this end are reversed.
* `Common`: Specified in [Common.thy](Common.thy). Is used to reverse the elements from the previous phase again to get them in the original order.

Each phase contains a `current` state, which holds the original elements of the deque end. 

*Functions:*

* `push`, `pop`: Add and remove elements using the current state.
* `invariant`: Defines an invariant which need to be kept during the two transformation phases.
* `tick`: Executes one step of the transformation, while keeping the invariant.
* `newSize`: Returns the size, that the deque end will have after the transformation is finished.
* `size`: Minimum of `newSize` and the number of elements contained in the current state.
* `remainingSteps`: Returns how many steps are left until the transformation is finished.
* `toList`: List abstraction of the elements which this end will contain after the transformation is finished
* `toCurrentList`: List abstraction of the elements currently in this deque end.

[Common](Common.thy)

The last two phases of both deque ends during transformation:

* `Copy`: Using the `tick` function the new elements of this deque end are brought back into the original order.
* `Idle`: The transformation of the deque end is finished.

Each phase contains a `current` state, which holds the original elements of the deque end. 

*Functions:*

* `push`, `pop`: Add and remove elements using the `current` state.
* `toList`: List abstraction of the elements which this end will contain after the transformation is finished
* `toCurrentList`: List abstraction of the elements currently in this deque end.
* `tick`: Executes one step of the transformation, while keeping the invariant.
* `remainingSteps`: Returns how many steps are left until the transformation is finished.
* `newSize`: Returns the size, that the deque end will have after the transformation is finished.
* `size`: Minimum of `newSize` and the number of elements contained in the `current` state.

[Current](Current.thy)

This data structure is composed of:

 * the newly added elements to one end of a deque during transformation phase
 * the number of these newly added elements 
 * the originally contained elements
 * the number of elements which will be contained after the transformation is finished.

*Functions:*

* `put`, `get`, `top`, `bottom`: Add and remove elements.
* `toList`: List abstraction for the originally contained elements of a deque end during transformation.
* `invariant`: Is the stored number of newly added elements correct?
* `size`: The number of the originally contained elements.
* `newSize`: Number of elements which will be contained after the transformation is finished.

[Stack_Proof.thy](Stack_Proof.thy), [Current_Proof.thy](Current_Proof.thy), [Common_Proof.thy](Common_Proof.thy), [Small_Proof.thy](Small_Proof.thy), [Big_Proof.thy](Big_Proof.thy) and [Transformation_Proof.thy](Transformation_Proof.thy) contain the proofs on of the operations of the respective data structures based on the specified invariants and list abstractions.

[RealTimeDeque_Dequeue.thy](RealTimeDeque_Dequeue.thy), [RealTimeDeque_Enqueue.thy](RealTimeDeque_Enqueue.thy) and [RealTimeDeque_Proof.thy](RealTimeDeque_Proof.thy) use these proofs to prove the deque specification from [Deque.thy](Deque.thy) for the RealTimeDeque implementation.



