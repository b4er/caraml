theory Index
  imports CaraML_Site
begin

\<comment> \<open>the landing page: no reader profile, since nothing here is gated\<close>
page (control: none) \<open>CaraML\<close>

div (hero) \<open>
  html \<open><img class="hero-logo" src="assets/caraml-logo.svg" alt="">\<close>
  \<open>A strict functional programming language in the ML family, with a compiler verified in
   Isabelle/HOL.\<close>
\<close>

caraml \<open>effect File {
  fopen : Str -> Nat;
  read : Nat -> Nat
}

main =
  with f = handler {
    fopen p -> openFile p;
    read h -> readByte h
  }
  print (f.read (f.fopen "data"))  -- the file is opened before it is read\<close>

html \<open><p class="actions">
  <a class="button" href="Get_Started.html">Get started</a>
  <a class="button secondary" href="Tools.html">Documentation</a>
</p>\<close>

section \<open>What you get\<close>

div (features) \<open>
  div (feature) \<open>
    subsection \<open>Formally verified\<close>
    \<open>Machine-checked in Isabelle/HOL: well-typed programs never crash,
     and compilation preserves I/O behaviour down to the target code.\<close>
  \<close>
  div (feature) \<open>
    subsection \<open>Total by default\<close>
    \<open>Function types carry their (named) effects - no unstated side-effects.
    Divergence is an effect too, so a pure type means a total function.\<close>
  \<close>
  div (feature) \<open>
    subsection \<open>Multi-shot handlers\<close>
    \<open>A \<open>handler\<close> clause binds the resumption as an ordinary value.
     Call it once, many times, or never.\<close>
  \<close>
  div (feature) \<open>
    subsection \<open>Modular implicits\<close>
    \<open>Interfaces are signatures, instances are modules, nothing is canonical.
     Implicit arguments are elaborated from the instances in scope.\<close>
  \<close>
  div (feature) \<open>
    subsection \<open>Statically interpreted modules\<close>
    \<open>ML signatures, functors and sealing, compiled away by static
     interpretation. Expressive abstraction without runtime indirection.\<close>
  \<close>
  div (feature) \<open>
    subsection \<open>Recursion schemes\<close>
    \<open>Every \<open>type\<close> gets an \<open>Inductive\<close> instance from the
     compiler: a generic fold, with termination for free.\<close>
  \<close>
  div (feature) \<open>
    subsection \<open>Layout syntax\<close>
    \<open>UTF-8 source, user-defined operators, blocks by braces or by indentation.
     No preprocessor, no fixity tables.\<close>
  \<close>
  div (feature) \<open>
    subsection \<open>Separate compilation\<close>
    \<open>One file compiles to one module. Modules link after compilation, nothing
     is recompiled twice.\<close>
  \<close>
\<close>

section \<open>Where to go next\<close>

text \<open>
  \<^item> \<^url>\<open>Get_Started\<close> is the tutorial: a first program,
   a call across the foreign boundary.
  \<^item> \<^url>\<open>Compiler\<close> describes the Isabelle/HOL
   formalization of the compiler implementation.
\<close>

end
