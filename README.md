# Lean 4 Mathematics Proofs Collection

This repository contains a collection of formal mathematical proofs written in Lean 4, a powerful proof assistant and functional programming language. The goal is to build a library of foundational mathematical proofs that serve both as learning resources and as verified mathematical truths.

## Project Structure

Each mathematical topic has its own dedicated library with specialized modules:

For example, the `OddNumbers` library contains proofs related to odd and even numbers.

- **OddNumbers**: Proofs about odd and even number properties
  - `Parity.lean`: Definitions of odd and even numbers
  - `Basic.lean`: Fundamental theorems about odd and even numbers

## Current Theorems

### Odd and Even Numbers

- **odd_square_of_odd**: The square of an odd number is odd
- **odd_mul_odd**: The product of two odd numbers is odd
- **odd_sum_even**: The sum of two odd numbers is even

## Getting Started

### Prerequisites

- Lean 4 (version 4.5.0 or later)
- Lake (Lean's package manager)
- A compatible editor with Lean support (e.g., Visual Studio Code with the Lean 4 extension)
- Basic knowledge of Lean syntax and theorem proving

### Installation

1. Install Lean and elan (the Lean version manager):
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

2. Clone this repository:
   ```bash
   git clone https://github.com/yourusername/lean-proofs.git
   cd lean-proofs
   ```

3. Build the project:
   ```bash
   lake build
   ```

### Creating a New Proof

To add a new proof to an existing library (e.g., OddNumbers):

1. Open the appropriate module file (e.g., `OddNumbers/Basic.lean`)
2. Add your theorem and proof
3. Build and verify:
   ```bash
   lake build
   ```

To create a new mathematical topic:

1. Create a new directory and module files:
   ```bash
   mkdir NewTopic
   touch NewTopic.lean
   touch NewTopic/Basic.lean
   ```

2. Update `lakefile.lean` to include your new module

## Learning Resources

- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)


