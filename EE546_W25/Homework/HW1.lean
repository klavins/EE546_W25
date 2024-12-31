
import Mathlib.Data.Nat.Prime.Defs

/- # HOMEWORK 1 : DUE MON JAN 13, 2024 (by Midnight) -/

/- # PRE-EXERCISES

a. Create a Mathlib-based project using EE546_Lastname as the project name. For example, if your name is Allen Turing, then you would name your project EE446_Turing.

b. Edit the file `Basic.lean` so that it has the code from the "TESTING YOUR INSTALLATION" section above. Make sure it works.

c. Create a file called `HW1.lean` in the same directory as Basic.lean.

d. Make a github repo for you project using the same name. You will use this repo to turn in your homework. Make the repo private and share it with `klavins` so I can access it. Initially I will do

  git clone https://github.com/turing/EE546_Turing.git

supposing your git username is `turing` to get your code. I will pull subsequent changes using:

  git pull origin master

from within that directory. Homework files should restate each problem (just copy and paste the problem statement. Textual answers should be written as comments. Lean code should be executable assuming Mathlib is installed and produce no errors. If you are stuck on part of a theorem, use `sorry` for partial credit. -/

/- # EXERCISES TO TURN IN

1. Describe procedures by which one might justify the following statements, or argue that they are not justifiable.

  - An Apple M4 chips has 28 billion transistors.
  - There is life Mars.
  - The universe is infinite.

2. How is a patent description a kind of knowledge represenation? Describe to what extent a patent might correspond to actual facts and whether and how it might be justifiable.

3. For each of the following areas, describe how knowledge is most commonly represented:

  - Electronic circuits
  - Mathematical theorems
  - Baking
  - Olympic weightlifting

4. (Lean) State and prove the theorems (as examples)

  False → False
  False → True
  True → True

5. (Lean) State the `Twin Prime Conjecture` as a theorem in Lean and put `sorry` as its proof. You can use the definition of primality in Mathlib by importing `Mathlib.Data.Nat.Prime.Defs` and using `Nat.prime`.

6. (Lean) Define a function called list_double that takes a list of natural numbers and returns a list in which each number is doubled. For example, list_double [2,5,7] would return [4,10,14]. Evaluate your function on a few examples.

# ADDITIONAL EXERCISES

i. Consider [this paper](https://www.nature.com/articles/483531a) in which authors attemped to repreduce 53 scientific results, but were only able to confrm 6. Apparantly either many published results are false, or what is published is not a complete description of the result. In the latter case, where might the remaining knowledge reside?

ii. For each of the following areas, describe how knowledge is most commonly represented:
    - Electronic circuits
    - Mathematical theorems
    - Baking
    - Olympic weightlifting

iii. Consider Ohm's law stating that V = IR. What experimental context needs to be given tho this statement for it to make sense? Are there examples where it is not true?

-/
