## Homework 9

The deadline for Homework 9 is Wednesday, November 22, 8pm. The late submission deadline is Tuesday, November 28, 4pm.

Refer to the homework handout [`hw09.pdf`](hw09.pdf) for details about the assignment. This file provides some information to help you get started with setting up your development environment for the homework assignments.

### Getting the code template

Before you perform the next steps, you first need to create your own
private copy of this git repository. To do so, click on the link
provided in the announcement of this homework assignment on
Brightspace. After clicking on the link, you will receive an email from
GitHub, when your copy of the repository is ready. It will be
available at
`https://github.com/nyu-popl-fa21/hw09-<YOUR-GITHUB-USERNAME>`.
Note that this may take a few minutes.

* Open a browser at `https://github.com/nyu-popl-fa23/hw09-<YOUR-GITHUB-USERNAME>` with your Github username inserted at the appropriate place in the URL.
* Choose a place on your computer for your homework assignments to reside and open a terminal to that location.
* Execute the following git command: <br/>
  ```bash
  git clone https://github.com/nyu-popl-fa23/hw09-<YOUR-GITHUB-USERNAME>.git hw09
  cd hw09
  ```

Please make sure that you clone the copy of your own version of this repository that is identified by your Github username, rather than the template repository.

The problems that you you should solve for this assignment are described in the file `hw09.pdf`.

The assignment consists of a non-coding part (Problem 1) and a coding part (Problem 2).

1. Your solutions to the non-coding parts of the assignment should be either put in a plain text file called `solution.md`, or a PDF file called `solution.pdf`. Scans of clearly readable hand-written solutions are also accepted. Please stick to this naming scheme.

2. The code template for solving Problem 2 is provided in the file 
   ```
   src/main/scala/popl/hw09.scala 
   ``` 
   relative to the root directory of the repository. Follow the instructions in the
   [in-class-code](https://github.com/nyu-popl-fa23/in-class-code)
   repository to import the project into InteliJ (or use your other
   favorite IDE or editor to work on the assignment).

   You can implement the solutions by replacing the `???`
   expressions in `hw09.scala` with your code for the corresponding
   part. Please do not modify the signatures of the given function
   definitions (i.e. do not change the names of these functions, their
   arguments, or their return types).


### Submitting your solution

Once you have completed the assignment, you can submit your solution
by pushing the modified code template to GitHub. This can be done by
opening a terminal in the project's root directory and executing the
following commands in the terminal:

```bash
git add .
git commit -m "solution"
git push
```

You can replace "solution" by a more meaningful commit message.

Refresh your browser window pointing at
```
https://github.com/nyu-popl-fa23/hw09-<YOUR-GITHUB-USERNAME>/
```
and double-check that your solution has been uploaded correctly.

You can resubmit an updated solution anytime by reexecuting the above
git commands. Though, please remember the rules for submitting
solutions after the homework deadline has passed.

### Testing your code

To test your code against the provided unit tests you can follow the same instructions as for Homework 1.
In addition to the unit tests, you will find some test JavaScript files in the directory `testjs` of the repository.

When you start sbt in the root directory of the repository and execute the `run` command with one of the files in `testjs` as input, the expression in the file will be parsed into a value of type `Expr` (i.e., the Scala representation of the JavaScript subset that we are considering). 
The parsed expression is then passed to your implementation of the interpreter (the function `eval` defined in `hw09.scala`). For instance, to run your interpreter on the file `testjs/test01_arith.js`, you can execute the following command from the command line:

```bash
$ sbt "run testjs/test01_arith.js"
```

Alternatively, if you are already inside of the sbt shell, execute:

```
sbt:hw09> run testjs/test01_arith.js
```

If you add the option `-d` as additional argument to the run command, you will see some useful debug output, such as the pretty printed AST representation of the parsed input expression.

Alternatively, you can run the interpreter directly from inside the IDE. To do so, right-click the file `hw09.scala` and select "More Run/Debug" and then "Modify Run Configuration". You can provide the command line arguments to the interpreter in the text field labeled "Program arguments". Enter e.g. "testjs/test01_arith.js" in this field and click "OK". When you now right-click on the file `hw09.scala` and select "Run 'hw09'", then the interpreter will be executed with the specified command line arguments.

I suggest that you run your implementation on the provided JavaScript files once all the unit tests are passing.

In general, I strongly advise you to write your own additional unit tests and JavaScript test files to further increase your confidence that your implementation of the interpreter is correct.


### Debugging

As the complexity of your interpreter code increases over the next homework assignments, you will sooner or later start to introduce debugging output in your interpreter. In particular, you will probably want to pretty print the Scala representation of JavaScript expressions. There are two ways to pretty print Scala values `e` of type `Expr`. Use

* ```println(e.prettyJS)``` to print an expression `e` in concrete JavaScript syntax
* ```println(e)``` to print an expression `e` as an abstract syntax tree represented as a Scala algebraic data type

One other useful feature that the parser provides for helping with debugging is that it decorates every expression of the parsed JavaScript input file with the position (i.e. line and column number) from which it originated in the input file. Given a value `e` of type `Expr`, you can access the source code line and number with `e.pos.line` and `e.pos.column`, respectively. 
