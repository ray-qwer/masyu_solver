# MASYU SOLVER by MINISAT
## Introduce of Masyu
Masyu(ましゅ,魔手),named as pearl, is a type of logic puzzle designed and published by Nikoli. [wiki](https://en.wikipedia.org/wiki/Masyu)

### Rule
Masyu is played on a rectangular gird of squares, and some of which contain pearls: white pearls or black pearls. The terminal goal is to find out a continuous non-intersecting cycle that goes through every pearls on the puzzle. 
the loop must pass through the pearlss by some additional rules:
- white pearl: must be traveled straight through, the loop must have at least a corner in the previous or next grid in its path.
- black pearl: must be a corner,and the loop must travel straight through the next and previous grid in its path 

![](https://i.imgur.com/VXkkyNO.png) ![](https://i.imgur.com/hbAqWCH.png)
You can try yourself [here](https://www.chiark.greenend.org.uk/~sgtatham/puzzles/js/pearl.html).

### NPC problem
it was proved by Erich Friedman([paper](https://www.researchgate.net/publication/2532689_Pearl_Puzzles_are_NP-complete)). He reduced Hamiltonian cycle to masyu by a tricky way. As the result, we can try to solve masyu puzzle by sat solver.

## Required
c\++11 up
compile by g\++

## demo
origin
![](https://i.imgur.com/YVZAoQu.png) 

output
![](https://i.imgur.com/BejM8XV.png)

verify
![](https://i.imgur.com/q8FexN6.png)

## SAT Queries
- loop constraint: every grid will have two lines or zero lines connect to it. The grids have pearls always have two lines connect to it.
- pearl constraint: need to follow the rule of black/white rules
- single loop constraint: with the constraints above, it might produce multiple loops rather than single loop, therefore we need to do DFS to find out if the loop is single or not by checking if all pearls in one cycle.

## SAT Variables
- vertex variables: every grid is a vertex.
    - All vertex need to follow loop constraint. If vertex satisfies the rule, vertex is **True**.
    - the puzzle is SAT iff all vertex is True
- edge variables: the connection between two vertex. 
    - A edge variable is **True** iff it is part of loop.

## Usage

### graph format

\<num of height> \<num of width>
\<the puzzle you want to solve, "." if the grid is empty, "b" for black, "w" for white >

eg.
![](https://i.imgur.com/XaXbB5a.png)

format:
```
6 6
..bb..
......
.w....
.w..bw
.....w
..w...
```
### run the code

#### normal use
```
.\Masyu -f <puzzle format file, eg. problem_set\p4>
```
or you can load input manually by
```
.\Masyu -m 
```
#### modifying files
if you want modify the files, then do
```
make
```
after you finish modify.
