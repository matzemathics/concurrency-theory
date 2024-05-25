import «CtLean».Basic

variable [LTS P] (p q: P)


structure LTS.Edge (p: P) where
  act: LTS.Act P
  dest: P
  prop: transition p act dest

inductive LTS.Path: P → Type
| nil (p: P): Path p
| cons {p p': P} (ps: Path p) (e: Edge p) (h: e.dest = p'): Path p'

def LTS.Path.orig: ∀{p: P}, (LTS.Path p) → P
| p, nil _ => p
| _, cons ps _ _ => ps.orig


def Simulate (p q: P) (map: ∀(p: P), LTS.Edge p → P → P): Nat → Prop
| 0 => True
| .succ n => ∀(e: LTS.Edge p),
  (LTS.transition q e.act (map p e q) ∧ Simulate e.dest (map p e q) map n)

structure Bisimulation' where
  sim: ∀(p: P), LTS.Edge p → P → P
  sym: ∀{a}, ∀{p p' q}, ∀t, ∀t', sim q ⟨a, sim p ⟨a, p', t⟩ q, t'⟩ p = p'
  coind_l: ∀n, Simulate p q sim n
  coind_r: ∀n, Simulate q p sim n

def Bisimilar' := Nonempty (Bisimulation' p q)

def SelfSim: Bisimulation' p p where
  sim p e _ := e.dest
  sym _ _ := rfl
  coind_l n := by
    induction n generalizing p with
    | zero => trivial
    | succ n ih => refine fun ⟨_, _, prop⟩ => ⟨prop, ih _⟩
  coind_r n := by
    induction n generalizing p with
    | zero => trivial
    | succ n ih => refine fun ⟨_, _, prop⟩ => ⟨prop, ih _⟩

theorem Bisimilar'.refl: Bisimilar' p p :=
  ⟨SelfSim p⟩

def InvSim (h: Bisimulation' p q): Bisimulation' q p where
  sim := h.sim
  sym := h.sym
  coind_l := h.coind_r
  coind_r := h.coind_l

theorem Bisimilar'.symm: Bisimilar' p q → Bisimilar' q p :=
  fun ⟨h⟩ => ⟨InvSim _ _ h⟩

structure BisimCond: Prop where
  left: LTS.transition p a p' → ∃q', (LTS.transition q a q' ∧ Bisimilar p' q')
  right: LTS.transition q a q' → ∃p', (LTS.transition p a p' ∧ Bisimilar p' q')

theorem BisimCond.refl: BisimCond p p where
  left t := ⟨_, ⟨t, Bisimilar.refl _⟩⟩
  right t := ⟨_, ⟨t, Bisimilar.refl _⟩⟩

theorem BisimCond.symm (h: BisimCond p q): BisimCond q p where
  left t := by
    have ⟨_, ⟨t', h'⟩⟩ := h.right t
    refine ⟨_, ⟨t', h'.symm⟩⟩

  right t := by
    have ⟨_, ⟨t', h'⟩⟩ := h.left t
    refine ⟨_, ⟨t', h'.symm⟩⟩

theorem show_cond: Bisimilar' p q → BisimCond p q := by
  intro ⟨sim, sym, coind_l, coind_r⟩
  constructor
  . intro _ _ t
    let e: LTS.Edge _ := ⟨_, _, t⟩
    exists (sim p e q)
    constructor
    . exact (coind_l 1 e).left
    . refine ⟨sim, sym, ?_, ?_⟩
      . intro n
        refine (coind_l n.succ e).right
      . intro n
        let e': LTS.Edge _ := ⟨_, _, (coind_l n.succ e).left⟩
        have := sym e.prop e'.prop ▸ (coind_r n.succ e').right
        exact this
  . intro _ _ t
    let e: LTS.Edge _ := ⟨_, _, t⟩
    exists (sim q e p)
    constructor
    . exact (coind_r 1 e).left
    . refine ⟨sim, sym, ?_, ?_⟩
      . intro n
        let e': LTS.Edge _ := ⟨_, _, (coind_r n.succ e).left⟩
        have := sym e.prop e'.prop ▸ (coind_l n.succ e').right
        exact this
      . intro n
        refine (coind_r n.succ e).right

noncomputable def sim [DecidableEq P] {p q: P} (h: BisimCond p q):
  ∀(p': P), LTS.Edge p' → P → P := fun p ⟨a, p', t⟩ q =>
    sorry

theorem sim_edge [DecidableEq P]: (t: LTS.transition p a p') →
  LTS.transition q a (sim h _ ⟨_, _, t⟩ q) :=
  sorry

theorem sim_cond [DecidableEq P] (h: BisimCond p q)
  (lp: {ps: LTS.Path p' // ps.orig = p})
  (rp: {qs: LTS.Path q' // qs.orig = q}):
  ∀n, Simulate p' q' (sim h) n := by
  intro n; cases n; trivial
  case succ n' =>
    intro e
    constructor
    . apply sim_edge
    . apply sim_cond
      . refine ⟨LTS.Path.cons lp.val e rfl, lp.property⟩
      . let e' : LTS.Edge _ := ⟨_, _, sim_edge (h:=h) p' q' e.prop⟩
        refine ⟨LTS.Path.cons rp.val e' rfl, rp.property⟩
