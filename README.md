# The Spinnaker programming language
- [The generali idea](#idea)
	- [Target audience](#target)
- [Features](#features)
	- [Basics](#basics)
	- [Type relations and instance resolution](#types)
	- [Easy lists](#lists)
	- [Lets, binds, patterns](#lets)
	- [More types](#types)
	- [Mutual recursion](#recursion)
	- [Modules](#modules)
	- [FFI (sort of)](#ffi)
- [Roadmap](#roadmap)

Compile any example with `cabal run spinnaker -- -f=example_source_path`  (if you don't want to install the compiler on your system), this will output an `out.js` , which you can run with `node` or `bun`.
It probably won't work on Windows, but I haven't tested it.

## The general idea <a name="idea"></a>
Spinnaker is a purely functional, eagerly evaluated programming language. It's design lies somewhere between Haskell, PureScript and Roc, while it's syntax has had some opinionated changes (for example being whitespace-insensitive).
I have no previous experience in compilers or computer science, but I decided to start implementing the language as a way to explore the problem space and figure out the best architecture. My end goal would be to rewrite the compiler from scratch once I'm satisfied with the features I implemented and how to do it.
I've written my own parsing combinator library and command line argument parser. Of course, they don't work as well as the libraries available, but I want to '*reinvent the wheel*' as much as possible.

### Target audience <a name="target"></a>
I decided to make a programming language when I realized that no existing one offered the exact blend of features I wanted. For example, Haskell is awesome, but I don't really like whitespace-sensitivity or lazy evaluation.
As such, don't expect Spinnaker to have some fancy new feature you've never heard of before, or to be revolutionary in any sense. This language will be as good as it needs to be to justify using it over other languages in my own projects.
This document is not intended to sell you on the language, but showcase it to people that might be interested in offering feedback on it.

## Features <a name="features"></a>
### Basics <a name="basics"></a>
Spinnaker enables brevity. Here is a very simple Hello World:
```
def main = Core.putStrLn "Hello, World!"
```
Lambdas are the heart of the language, hence they require minimal syntax.
Spinnaker features polymorphic type inference at the top-level:
```
def compose = \f, g, x -> f (g x)
```
Operators are easy to define, they are all right-associative and have the same precedence. All operator sections are supported.
```
def (<|) = compose

def add = (+)
def add1 = (1 +)
def sub3 = (- 3)
```
Keep in mind that the space between the minus sign and the three is significant. If it weren't there the parser would read an integer literal of value `-3`. This doesn't apply to the plus sign.

Type relations (analogous to Haskell's MultiParamTypeClasses) provide a mechanism for terse ad-hoc polymorphism:
```
def string_true_5 = show True ++ show 5
```
Pattern matching is concise:
```
def and = \x, y ->
	put x, y
	| True, True -> True
	| _, _ -> False
```
You can also write pattern-matching lambdas:
```
def and =
	\ True, True -> True
	| _, _ -> False

def head =
	\ [] -> error "Error message here"
	| [x | _] -> x
```
Spinnaker supports monadic IO, which can be nicely perfomed with the `bind` syntax:
```
use Std

def main =
	_ <- putStr "What's your name? ";
	name <- getLn;
	putStrLn $ "Hello, " ++ name ++ "!"
```
You may have noticed that `main` has different types in these examples. We can get away with it because the compiler leverages the power of type relations to choose the best implementation of the entry point. This behavior is extensible to user-defined types by implementing the `ProgramTop` relation.

### Type relations and instance resolution <a name="typerels"></a>
You can define type relations, for example the classic `Functor` and `Monad`:
```
rel pub Functor f = fmap : forall a b. (a -> b) -> f a -> f b

# A Monad relation requires a Functor super-relation
rel pub {Functor m} => Monad m =
	return : forall a. a -> m a,
	bind : forall a b. m a -> (a -> m b) -> m b
```
An example of an instance:
```
inst Functor Maybe {
	def fmap =
		\ _, None -> None
		| f, Some x -> Some (f x)
}
```
Overlapping instances are permitted, Spinnaker always chooses the most specific instance. If it can't, it fails. This can be useful, for example, to avoid implementing a `Functor` for every `Monad` if you don't want to, but you can still provide an efficient implementation for a specific type, which the compiler will choose.
In fact, the standard library provides this instance:
```
inst forall m. {Monad m} => Functor m {
	def fmap = \f, m -> bind m (f |> return)
}
```

### Easy lists <a name="lists"></a>
There's special syntax for lists, which refer to a user-defined `List` type in the standard library. For example, this removes the second element of a list:
```
def remove_second : forall a. [a] -> [a]
	= \[x, x' | xs] -> [x | xs]
```

### Lets, binds, patterns <a name="lets"></a>
Let and bind syntaxes respectively reduce to pattern matching and lambdas, so you can use any valid pattern in them.
```
let <any pat> = e0 -> e1
#same as
put e0 | <any pat> -> e1

<any pat> <- e0; e1
#same as
bind e0 (\<any pat> -> e1)
```

### More types <a name="types"></a>
Data types are defined as you'd expect:
```
data Either a b = Left a | Right b
```
Type synonyms are experimental:
```
typesyn String = [Chr]
typesyn Point a = (a, a)
```
You can provide type annotations to top-level definitions and expressions. While they are generally not needed, they are sometimes necessary to specify relation instances:
```
def fac : Int -> Int =
	\ 0 -> 1
	| n -> n * fac (n - 1)

def map : forall a b. (a -> b) -> [a] -> [b] =
	\ _, [] -> []
	| f, [x | xs] -> f x :: map f xs

def false = toEnum 0 : Bool
```

### Mutual recursion <a name="recursion"></a>
To aid type inference and clarity, mutually recursive values must be defined together with the `and` keyword.
```
def isEven =
	\ 0 -> True
	| n -> not $ isOdd $ n - 1

and isOdd =
	\ 0 -> False
	| n -> not $ isEven $ n - 1
```
This also works for data types (but not for type synonyms):
```
data A a b = NilA a | ConsA a (B a b)
and B a b = NilB b | ConsB b (A a b)
```

### Modules <a name="modules"></a>
You can define modules and import them from files:
```
# ./a.spk
def pub answer_to_everything = 42

mod pub Nums {
	def pub five = 5
}

# ./main.spk
mod A "a.spk"
use A

def main = answer_to_everything + Nums.five
```

### FFI (sort of) <a name="ffi"></a>
As of now, you can only use functions defined in the host language (which, at the moment, is just the `js` backend). They can be declared in Spinnaker as follows (note that they must be monomorphic):
```
ext someExternalFunction "functionName" : Int, Flt -> Bool

def getABool = someExternalFunction 3 1.2
```
This compiles to the following `js` call:
```
functionName(3, 1.2)
```
Such approach fails when considering user-defined or polymorphic types, but it's sufficient to define a basic runtime.

## Roadmap <a name="roadmap"></a>
- Expand the standard library
- Tuple sections
- Compilation to a C subset
- Decent error messages
- Support for defining libraries
- Automatic generation of documentation from sources
- The compiler is painfully slow, this needs fixing
- Tail-call optimization
- Redefine an FFI (in particular, value exports)
- Maybe implement the Perceus technique
- Still on the fence about records and row polymorphism
