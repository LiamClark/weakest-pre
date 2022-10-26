# Pothos, Iris based separation logic for monadic languages

This is the formalization of Pothos, all logics described in the thesis can be found here.
## Requirements
* Coq 8.13.2
* Iris should be installed on your machine, instructions can be found [here](https://gitlab.mpi-sws.org/iris/iris#working-with-iris). Pothos is guaranteed to work with Iris version: dev.2021-11-26.0.255341dd

## Structure
In the thesis we present three logics one for the state monad, delay monad and interaction trees.
* The definition for the state monad can be found in `state.v` and its corresponding logic in `statewp.v`
* The delay monad implementation can be found in `delaystate.v` and the corresponding logic can be found in `delaywp.v`, note that there is an extra monad included here that is not in the thesis.
Minimal verification examples can be found in `delay_examples.v`
* Finally the implementation of itrees can be found in `itree.v`. The interpreter can be found in `evaluation.v`. The logic can be found in `itreewp.v`. The case study can be found in `itree_examples.v`.