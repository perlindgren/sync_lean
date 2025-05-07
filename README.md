# sync_lean

Synchronous Circuit Simulator, the Lean way.

This repository explores the possibility of modelling and simulating synchronous circuits in Lean. The main idea is to split the design into two distinct classes of components:

- Synchronous logic, registers with input and output synchronized by a clock.

- Combinational logic, components that evaluate inputs to outputs.

---

## Simulator

The simulator state is holding a list of registers, implementing the `Clock` type class interface, along with a list of components, implementing the `Combinational` interface.

Simulating a cycle amounts to first update all registers (`clock`), followed by evaluating the components (`evaluate`) in topological order.

In this way SyncLean is similar to SyncRim (Rust implementation) and its predecessor SyncSim (Java implementation). 

Exactly how the type classes and simulator store should look like is not yet clear.

## Components

For now only a simple generic multiplexer and a generic adder has bin implemented. 

### Mux

The `mux` is generic both to the number of inputs and their width. The select signal requires a proof that the number of bits is exactly sufficient for choosing the input, and that select signal value is in range of the `Vector` of inputs. A default proof provides automation for simple use cases.

### Adder

The adder is built ground up from FullAdder components, generic to the bit-width. For (any) concrete assignment of bit-width, the model can be proven by `bv_decide` to comply to the specification of BitVec additions. Due current limitations in proof validation implementation in Lean, sizes no larger than 16 is recommended (for proofs).





