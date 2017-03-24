# An Implementation of Various Linear Logics in Agda (ALL)

Design
------

The design of ALL is based the following:

  - Haskell Frontend:     
     - Repl:
       - Haskeline
  - Agda Backend:
     - Parsers (written in combined Agda/Haskell):
       - Alex
       - Parsec
     - Type Checker
     - Evaluator
     - Formal verification:
       - Dialectica categories
       - Petri nets
     - Pretty Printer

The Agda backend will be a "server" that will take in various
command-line options and a linear-logic expression that will then be
parsed by a combined Agda/Haskell parser.  The parser will turn the
input expression into an intermediate representation -- without
locally-nameless -- that will be shared between both Haskell and Agda
using the FFI, but then will be translated into locally-nameless
representation on the Agda side.