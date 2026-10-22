theory Compiler
  imports CaraML_Site CaraML_Spec.Pipeline
begin

page (part: compiler, order: 10, optional: 60) \<open>Compiler\<close>

text \<open>
  The compiler takes a program from source text to machine code through a chain of
  intermediate languages. The diagram lists the languages on the left and the passes
  between them in the middle. The right column names the theorem each pass has, or says
  what it lacks.
\<close>

text \<open>
  From the explicit surface down, every pass is a @{const Pipeline.phase}: when it
  compiles \<open>p\<close> to \<open>q\<close>, the behaviours of \<open>q\<close> are among those of \<open>p\<close>,
  up to running out of resources.
\<close>
doc_thm (display) \<open>Pipeline.phase.compile_correct\<close>
expert \<open>
  text \<open>
    A behaviour is what one run of a program shows the host: it terminates with an
    outcome after a finite trace of events, it diverges with an infinite stream of
    events, or it fails.
  \<close>
  source (kind: type) \<open>Pipeline.outcome\<close>
  source (kind: type) \<open>Pipeline.behaviour\<close>
  text \<open>
    A compiled program may run out of resources where its source did not. For every
    behaviour in \<open>B\<close> and every finite prefix \<open>io\<close> of its events,
    @{const Pipeline.ext} adds the run that stops with \<open>ResourceExhausted\<close> after
    \<open>io\<close>. @{const Pipeline.prefix_of} says what a prefix of a behaviour is.
  \<close>
  source \<open>Pipeline.prefix_of\<close>
  source \<open>Pipeline.ext\<close>
  text \<open>
    Refinement allows the target exactly that: every behaviour of the target is one of
    the source's, or one of them cut short by exhaustion. A source that may fail
    promises nothing, so every target refines it.
  \<close>
  source \<open>Pipeline.refines\<close>
  text \<open>
    A phase is a compiler between two languages whose output refines its input, for
    every state of the host.
  \<close>
  source \<open>Pipeline.phase\<close>
\<close>
text \<open>
  Phases compose by @{thm Pipeline.phase_compose}. The compiler's theorem
  \<open>caraml_correct\<close> is the chain from the explicit surface to LabLang as one phase,
  for every target that interprets the locale \<open>machine\<close>. It rests on
  \<open>typed_safe\<close>, whose last step, protocol adherence, is open (Pillar B). From Core
  down, every pass is also a @{const Pipeline.separate_phase}: compiling two modules and
  linking the results gives what compiling the linked source gives, and linking
  appends. The dotted lines mark where each property starts.
\<close>

div (id: "compiler", pipeline) \<open>
  div (lang, done) \<open>source text (UTF-8)\<close>

  div (tag: details, stage, "open": "open") \<open>
    div (tag: summary) \<open>
      div (title) \<open>Front end\<close>
      div (what) \<open>Front end: parse, desugar, infer types, effects, protocols\<close>
      div (chip) \<open>\<close>
    \<close>
    div (tag: details, pass, stub, cross, partial, "data-fails": "the lexer; the parser") \<open>
      div (tag: summary) \<open>
        div (what) \<open>Decode UTF-8, lex and parse concrete syntax\<close>
        div (chip) \<open>parser: stub, rewrite pending\<close>
      \<close>
      \<open>Nothing below depends on concrete syntax: every theorem is stated on the surface
       AST. A verified parser would add one round trip, print then parse is the identity,
       and no more.\<close>
    \<close>
    div (lang, done) \<open>Surface AST: modules, functors, sealing, effects, named handlers,
      protocols\<close>
    div (tag: details, pass, done) \<open>
      div (tag: summary) \<open>
        div (what) \<open>Desugar fun clauses into curried fn + match\<close>
        div (chip) \<open>emitted by the checker\<close>
      \<close>
      \<open>\<open>fun f p\<^sub>1 = e\<^sub>1 | f p\<^sub>2 = e\<^sub>2\<close> becomes one curried fn whose body
       matches on its arguments. The checker does this on the way in, so the typing rules
       only ever meet fn and match.\<close>
    \<close>
    div (tag: details, pass, done, cross, partial, "data-fails": "type inference") \<open>
      div (tag: summary) \<open>
        div (what) \<open>Infer types, effect rows and protocols, resolve implicit module
          args, exit if fail\<close>
        div (chip) \<open>tc_sound \<checkmark>

          typed_safe \<checkmark> up to protocols (B)\<close>
      \<close>
      \<open>Unification over types, effect rows and protocols at once; implicit module
       arguments are filled in from the signatures in scope. tc_sound: what the checker
       accepts is well typed. typed_safe: a well-typed program does not go wrong. Its
       proof assumes that a typed program follows its protocols, which is open
       (Pillar B).\<close>
    \<close>
  \<close>

  div (divider) \<open>div \<open>Below this line every pass is a phase: \<open>sem q \<sqsubseteq> sem p\<close>.\<close>\<close>

  div (lang, done) \<open>Explicit surface: every type-directed decision written out\<close>

  div (tag: details, stage, "open": "open") \<open>
    div (tag: summary) \<open>
      div (title) \<open>Static interpretation\<close>
      div (what) \<open>Static interpretation: modules, functors and sealing resolved;
        externs and tuples to Core\<close>
      div (chip) \<open>\<close>
    \<close>
    div (tag: details, pass, done) \<open>
      div (tag: summary) \<open>
        div (what) \<open>Static interpretation: modules \<rightarrow> flat names, functors \<rightarrow>
          dictionaries, sealing by realisations\<close>
        div (chip) \<open>static_interp_phase \<checkmark>\<close>
      \<close>
      \<open>A module becomes its flat bindings M.x, a functor a function over dictionaries,
       and a sealed type is replaced by the realisation the sealing hides. The theorem is
       the first refinement of the diagram: the Core program's behaviours are among the
       surface program's.\<close>
    \<close>
    div (tag: details, pass, done, cross) \<open>
      div (tag: summary) \<open>
        div (what) \<open>extern \<rightarrow> perform on %ffi.sym, tuples \<rightarrow> constructors\<close>
        div (chip) \<open>part of the same phase\<close>
      \<close>
      \<open>An extern declaration is a perform on the effect %ffi.sym, so the FFI is one
       more effect, answered by the host. The host sees each closure in an argument as a
       numbered handle and may not answer with code, so a compiled closure, a label and
       an environment, looks the same to it as the source function. Tuples are
       constructors of an anonymous datatype.\<close>
    \<close>
  \<close>

  div (divider) \<open>div \<open>Below this line every pass is a separate phase: linking is appending.\<close>\<close>

  div (lang, done) \<open>Core: module-free, nested matches, deep multi-shot handlers, named
    handlers with protocols\<close>

  div (tag: details, pass, done) \<open>
    div (tag: summary) \<open>
      div (what) \<open>Compile nested patterns into one-level matches on variables only\<close>
      div (chip) \<open>pm_separate_phase \<checkmark> (C2)\<close>
    \<close>
    \<open>Nested patterns become a tree of one-level matches, each on a variable, with the
     fall-through made explicit. The proof is a clocked simulation: the two sides do not
     take the same number of steps, so a clock is threaded and behaviours are compared up
     to it.\<close>
  \<close>

div (tag: details, stage, hyp, "open": "open") \<open>
  div (tag: summary) \<open>
    div (title) \<open>Optimise\<close>
    div (what) \<open>Optimise Core: fold constants, pick known clauses, inline, drop dead
      bindings, float lets\<close>
    div (chip) \<open>\<close>
  \<close>
  div (tag: details, pass, hyp) \<open>
    div (tag: summary) \<open>
      div (what) \<open>Fold constants: evaluate closed primitive applications,
        \<open>1 + 2 \<rightarrow> 3\<close>\<close>
      div (chip) \<open>proof: rewrite on values\<close>
    \<close>
    \<open>Evaluate a primitive applied to literals at compile time. Each rewrite is
     justified by the primitive's own semantics and leaves values alone, so the
     simulation is the identity on values and the proof is an induction on the
     rewrite, the smallest shape a phase can have.\<close>
  \<close>
  div (tag: details, pass, hyp) \<open>
    div (tag: summary) \<open>
      div (what) \<open>Case of known constructor: a match on a visible \<open>C(v\<dots>)\<close> picks
        its clause at compile time\<close>
      div (chip) \<open>proof: lockstep simulation\<close>
    \<close>
    \<open>A match whose scrutinee is a visible constructor application picks its clause
     statically. The order of passes matters here: after pattern compilation every
     match is one level deep, so the known constructor is one binding away and the
     clause is a plain substitution.\<close>
  \<close>
  div (tag: details, pass, hyp) \<open>
    div (tag: summary) \<open>
      div (what) \<open>Inline small non-recursive functions under a size budget\<close>
      div (chip) \<open>proof: clock shift\<close>
    \<close>
    \<open>Replace a call to a small, non-recursive, known function by its body; the budget
     bounds code growth and makes the pass terminate. A removed call is a removed step,
     so this is the first pass whose simulation needs a clock shift, the same device
     the machine needs.\<close>
  \<close>
  div (tag: details, pass, hyp) \<open>
    div (tag: summary) \<open>
      div (what) \<open>Drop dead bindings: an unused let whose right-hand side is a
        value\<close>
      div (chip) \<open>proof: lockstep + purity\<close>
    \<close>
    \<open>Only a let whose right-hand side is a value or a constructor application may
     go: in a language with effects, \<open>let _ = perform Op v in e\<close> is dead code the
     host can observe. Purity here is syntactic, which is cheap to prove and already
     covers most dead bindings.\<close>
  \<close>
  div (tag: details, pass, hyp) \<open>
    div (tag: summary) \<open>
      div (what) \<open>Float lets: \<open>let x = (let y = a in b) in c\<close> \<rightarrow>
        \<open>let y = a in let x = b in c\<close>\<close>
      div (chip) \<open>proof: binder bookkeeping\<close>
    \<close>
    \<open>Flattening nested lets exposes the other four passes to one another. It needs
     y not free in c, so names are freshened on the way: the binder bookkeeping that
     takes most of the lines in every proof of this column.\<close>
  \<close>
\<close>


  div (tag: details, stage, "open": "open") \<open>
    div (tag: summary) \<open>
      div (title) \<open>Lowering\<close>
      div (what) \<open>Lower to Slot: flat closures, a code table per unit, positions
        instead of names\<close>
      div (chip) \<open>\<close>
    \<close>
    div (tag: details, pass, done, cross) \<open>
      div (tag: summary) \<open>
        div (what) \<open>Convert closures: a closure captures exactly its free variables,
          trimmed records, code opaque at the FFI\<close>
        div (chip) \<open>cc_separate_phase \<checkmark> (C3)\<close>
      \<close>
      \<open>A closure records exactly its free variables, in a trimmed record, and its body
       refers to nothing outside. The host only ever sees handles, so it cannot tell a
       Core closure from a Flat one; the simulation relates the two pointwise on the
       captured variables.\<close>
    \<close>
    div (lang, done) \<open>Flat: flat closures, closed bodies\<close>
    div (tag: details, pass, done, cross) \<open>
      div (tag: summary) \<open>
        div (what) \<open>Hoist closed code into a code table per unit; labels relocated at
          link time, post-order from the counts\<close>
        div (chip) \<open>lift_separate_phase \<checkmark> (C4)\<close>
      \<close>
      \<open>Bodies move into a code table, one per unit; a closure is now a label and an
       environment. Labels are assigned post-order from the counts, which makes a unit's
       table relocatable: linking appends the tables and shifts the labels, and the proof
       shows the shift commutes.\<close>
    \<close>
    div (lang, done) \<open>Code: bodies in a table, a closure is a label and an
      environment\<close>
div (tag: details, pass, hyp) \<open>
  div (tag: summary) \<open>
    div (what) \<open>Known calls: when the callee is a statically known label, call it
      directly and skip the closure\<close>
    div (chip) \<open>needs: relocation commutes\<close>
  \<close>
  \<open>After lifting, a call to a closure whose label is manifest can jump to the label
   and skip the lookup. The catch is linking: labels are relocated when units are
   appended, so the rewrite must commute with relocation, which is what lift's
   theorem already tracks.\<close>
\<close>

    div (tag: details, pass, done, cross) \<open>
      div (tag: summary) \<open>
        div (what) \<open>Resolve names to positions: frame slots and record slots; globals
          stay by name for the linker\<close>
        div (chip) \<open>slots_separate_phase \<checkmark> (C5)

          backend_phase Core \<rightarrow> Slot \<checkmark>\<close>
      \<close>
      \<open>Locals become frame positions and record fields positions; globals keep their
       names, because linking is still appending bindings and must not renumber. The
       relation between environments is pointwise by position; continuations carry
       environments too, hence 74 cases.\<close>
    \<close>
  \<close>

  div (lang, done) \<open>Slot: nameless locals, records by position, globals by name\<close>

  div (tag: details, stage, "open": "open") \<open>
    div (tag: summary) \<open>
      div (title) \<open>Towards the machine\<close>
      div (what) \<open>Towards the machine: an explicit stack of frames, values as words in
        a heap\<close>
      div (chip) \<open>\<close>
    \<close>
    div (tag: details, pass, done, cross) \<open>
      div (tag: summary) \<open>
        div (what) \<open>Run on an abstract machine: explicit stack of frames, one tick per
          step; identity on programs (CEK by defunctionalisation)\<close>
        div (chip) \<open>slotm_phase \<checkmark> (C7)

          forward and backward by beh_sim\<close>
      \<close>
      \<open>Same programs, a different machine: an explicit stack of frames and one tick per
       step, the CEK machine obtained by defunctionalising the evaluator. The pass is the
       identity on code, so the theorem relates two semantics of Slot: the evaluator's
       induction forwards, clocks backwards.\<close>
    \<close>
    div (lang, done) \<open>SlotM: control, stack, name supply\<close>
    div (tag: details, pass, done, cross) \<open>
      div (tag: summary) \<open>
        div (what) \<open>Represent values as words: tagged blocks in memory, frames chained
          by cons cells, bump allocation, resource limit on exhaustion\<close>
        div (chip) \<open>heap_separate_phase \<checkmark> (C8)

          lockstep, refinement with Xlimit\<close>
      \<close>
      \<open>Values become tagged blocks in a word memory, small values immediates
       (\<open>2i+1\<close>, \<open>nil = 3\<close>), the stack and the globals chains of cons cells,
       allocation a bump pointer with no collector. The heap can run out where Slot could
       not, so the target may also stop with Xlimit, at equal clocks.\<close>
    \<close>
  \<close>

  div (lang, done) \<open>Heap: words in memory, cons-cell frames\<close>

  div (tag: details, choice, label: "Backend", "open": "open") \<open>
    div (tag: summary) \<open>
      div (title) \<open>Backend\<close>
      div (what) \<open>Backend: labelled assembly for a machine, or WebAssembly\<close>
      div (chip) \<open>\<close>
    \<close>
    div (option, label: "Assembly") \<open>
      div (tag: details, pass, done, cross, partial, "data-fails": "code generation") \<open>
        div (tag: summary) \<open>
          div (what) \<open>Generate code: a section per binding, runtime routines per
            section, protocols as state machines, marshal values to words\<close>
          div (chip) \<open>lab_separate_phase \<checkmark> (C9)

            caraml_correct at LabLang \<checkmark>\<close>
        \<close>
        \<open>Each binding becomes a section with its own copy of the runtime routines, so
         linking stays append; a perform site gets a frame walk specialised to its label,
         a protocol a state machine. Heap words lie in byte memory at the same addresses;
         values cross the FFI as words, in two calls. The generator refuses a program whose
         registers, layout or labels fail its checks; that no output of Slot fails them is
         not proved.\<close>
      \<close>
      div (lang, done) \<open>LabLang: labelled assembly, symbolic labels, byte memory, word
        FFI, link = append\<close>
div (tag: details, pass, hyp) \<open>
  div (tag: summary) \<open>
    div (what) \<open>Peephole: delete jumps to the next instruction, fuse move
      chains\<close>
    div (chip) \<open>proof: clock shift\<close>
  \<close>
  \<open>A local rewrite on straight-line code: a jump to the next instruction
   vanishes, a chain of moves fuses. Every deleted instruction is a step the
   target no longer takes, so the simulation is up to a clock shift, the same
   shape the encoding below already has.\<close>
\<close>

      div (tag: details, choice, label: "Target", "open": "open") \<open>
        div (tag: summary) \<open>
          div (title) \<open>Target\<close>
          div (what) \<open>Encode for a target: x86-64, ARMv8, RISC-V or ARMv7\<close>
          div (chip) \<open>\<close>
        \<close>
        div (option, label: "64 bit") \<open>
          div (choice) \<open>
            div (option, label: "x86-64") \<open>
              div (tag: details, pass, plan, cross) \<open>
                div (tag: summary) \<open>
                  div (what) \<open>Encode each instruction as x86-64 instructions;
                    simulation up to a clock shift (locale machine)\<close>
                  div (chip) \<open>planned

                    machine \<subseteq> backend \<checkmark>\<close>
                \<close>
                \<open>Each LabLang instruction becomes a few machine instructions; the locale
                 machine fixes what a target provides, and the simulation is up to a
                 clock shift. Every interpretation of machine inherits caraml_correct. None
                 is proved yet: x86-64 would be one, on the AFP model of the instruction
                 set.\<close>
              \<close>
              div (lang, plan) \<open>Assembly: x86-64, the AFP model\<close>
            \<close>
            div (option, label: "ARMv8") \<open>
              div (tag: details, pass, plan, cross) \<open>
                div (tag: summary) \<open>
                  div (what) \<open>Encode each instruction as AArch64 instructions: a
                    second interpretation of the locale machine\<close>
                  div (chip) \<open>planned

                    one interpretation\<close>
                \<close>
                \<open>A new target is one more interpretation of the locale machine: its
                 instruction set, its encoding of each LabLang instruction, and the clock
                 shift of the simulation. Nothing above LabLang changes, which is the
                 point of ending every backend in the same labelled assembly.\<close>
              \<close>
              div (lang, plan) \<open>Assembly: ARMv8 (AArch64)\<close>
            \<close>
            div (option, label: "RISC-V") \<open>
              div (tag: details, pass, plan, cross) \<open>
                div (tag: summary) \<open>
                  div (what) \<open>Encode each instruction as RV64 instructions: another
                    interpretation of the locale machine\<close>
                  div (chip) \<open>planned

                    one interpretation\<close>
                \<close>
                \<open>As for ARMv8: one interpretation of the locale machine. A load-store
                 architecture with many registers, so LabLang's fixed registers map one
                 to one and the clock shift per instruction is small.\<close>
              \<close>
              div (lang, plan) \<open>Assembly: RISC-V (RV64)\<close>
            \<close>
          \<close>
        \<close>
        div (option, label: "32 bit") \<open>
          div (choice) \<open>
            div (option, label: "ARMv7") \<open>
              div (tag: details, pass, plan, cross) \<open>
                div (tag: summary) \<open>
                  div (what) \<open>Encode for 32-bit words: the same compiler at
                    LENGTH = 32, then ARMv7 instructions\<close>
                  div (chip) \<open>planned

                    C9 needs 16 dvd LENGTH\<close>
                \<close>
                \<open>The backend is generic in the word length: C9 only asks for words of
                 whole, evenly many bytes, so 32 bits is the same compiler instantiated
                 again. Immediates and the heap limit shrink with the word, and a program
                 that fit at 64 bits may now stop with Xlimit.\<close>
              \<close>
              div (lang, plan) \<open>Assembly: ARMv7 (32-bit)\<close>
            \<close>
          \<close>
        \<close>
      \<close>
    \<close>
    div (option, label: "WebAssembly") \<open>
      div (tag: details, pass, hyp, cross) \<open>
        div (tag: summary) \<open>
          div (what) \<open>Emit WebAssembly: one dispatch loop (br_table), the heap in
            linear memory, the FFI an imported function\<close>
          div (chip) \<open>proof: against WasmCert-Isabelle\<close>
        \<close>
        \<open>Wasm has no jumps to arbitrary labels and no code addresses, so the split comes
         before LabLang; its stack holds no copyable frames (multi-shot handlers), so not
         before SlotM. Heap words map to linear memory, code indices to br_table cases,
         and memory.grow failing is Xlimit.\<close>
      \<close>
      div (lang, hyp) \<open>Wasm 1.0: structured control, linear memory, imported FFI\<close>
      div (tag: details, pass, hyp) \<open>
        div (tag: summary) \<open>
          div (what) \<open>Link: one function per binding in a shared table, run by a
            trampoline\<close>
          div (chip) \<open>keeps link = append\<close>
        \<close>
        \<open>One dispatch loop for the whole program would have to renumber every unit's code
         at link time. A function per binding, called through a shared table by a loop
         that is handed the next code index, keeps linking an append and never grows the
         native stack.\<close>
      \<close>
    \<close>
  \<close>
\<close>

end
