# README

This is a guide for contribution.

## Setup

First, fork this repository and clone your fork to your local. Then follow the commands below:

```bash
# You should clone your fork first.
# git clone <fork-repo-url>

cd Abstract-Algebra-in-Lean
# Install the required toolchain
elan install $(cat lean-toolchain)
# You can skip cache get step, but it will cause a long build.
lake exe cache get
lake build
```

## Propose new exercise

The issues contain exercises to be formalized. If you find some interesting exercise, you can propose it as an issue.

Please use latex to write mathematical formula and remember to follow the serial number.

## Pull request

Your formalized solution to some exercise in issues should be stored in `AbstractAlgebraInLean/Exercise/Ex{id}.lean`. For example, if you solve an issue named `Ex3`, then your file should be named `Ex3.lean`. You are encouraged to relate your PR with that issue, and use the same name.

Please make sure your code can compile successfully before opening a PR. It would be better for one PR to solve only one issue.