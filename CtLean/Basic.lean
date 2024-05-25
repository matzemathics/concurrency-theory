theorem Or.symm: (a ∨ b) → (b ∨ a)
| .inl h => .inr h
| .inr h => .inl h

class LTS (P: Type) where
  Act: Type
  transition: P → Act → P → Prop

variable [LTS P] (p q: P)

def Outgoing (a: LTS.Act P): Prop :=
  ∃p', LTS.transition p a p'

def LeftSim (r: P → P → Prop): Prop :=
  ∀{p p' q: P}, ∀ {a: LTS.Act P}, r p q →
    LTS.transition p a p' → ∃q', LTS.transition q a q' ∧ r p' q'

def RightSim (r: P → P → Prop): Prop := LeftSim (λp q ↦ r q p)

def Bisimulation (r: P → P → Prop) := LeftSim r ∧ RightSim r

def Bisimilar := ∃(r: P → P → Prop), r p q ∧ Bisimulation r

def IdentityRelation: α → α → Prop := (λx y ↦ x = y)

theorem diag_l_sim: LeftSim (P:=P) IdentityRelation := by
  intro _ p' _ _ h t
  exists p'
  refine ⟨?_, rfl⟩
  exact h ▸ t

theorem diag_sim: Bisimulation (P:=P) IdentityRelation := by
  refine ⟨diag_l_sim, ?_⟩
  simp [RightSim, IdentityRelation]
  conv => congr; intro p q; rw [Iff.intro Eq.symm Eq.symm]
  exact diag_l_sim

theorem Bisimilar.refl: Bisimilar p p := by
  exists IdentityRelation
  refine ⟨rfl, diag_sim⟩

def SymmetricClosure (r: α → α → Prop): α → α → Prop := fun x y => r x y ∨ r y x
def SC (r: α → α → Prop): α → α → Prop := SymmetricClosure r

theorem symm_l_sim (orig: Bisimulation r): LeftSim (P:=P) (SC r) := by
  intro p p' q _ h t
  cases h
  case inl h =>
    have ⟨_, ⟨t', h'⟩⟩ := orig.left h t
    refine ⟨_, ⟨t', .inl h'⟩⟩
  case inr h =>
    have ⟨_, ⟨t', h'⟩⟩ := orig.right h t
    refine ⟨_, ⟨t', .inr h'⟩⟩

theorem symm_r_sim (orig: Bisimulation r): RightSim (P:=P) (SC r) := by
  simp [RightSim, SymmetricClosure]
  conv =>
    congr; intro p q;
    delta SC SymmetricClosure;
    rw [Iff.intro Or.symm Or.symm]
  exact symm_l_sim orig

theorem symm_sim: Bisimulation r → Bisimulation (P:=P) (SymmetricClosure r) :=
  fun x => ⟨symm_l_sim x, symm_r_sim x⟩

theorem Bisimilar.symm {p q: P}: Bisimilar p q → Bisimilar q p := by
  intro ⟨r, ⟨h, t⟩⟩
  exists SymmetricClosure r
  refine ⟨.inr h, symm_sim t⟩

theorem trans_l_sim (orig: LeftSim r): LeftSim (P:=P) (TC r) := by
  intro p p' q a h t
  induction h generalizing p'
  case base h =>
    have ⟨_, ⟨t', h'⟩⟩ := orig h t
    refine ⟨_, ⟨t', .base _ _ h'⟩⟩
  case trans H h =>
    have ⟨_, ⟨t', h'⟩⟩ := H t
    have ⟨q', ⟨t'', h''⟩⟩ := h t'
    have := TC.trans _ _ _ h' h''
    exists q'

theorem trans_r_sim (orig: RightSim r): RightSim (P:=P) (TC r) := by
  intro p p' q a h t
  induction h generalizing p'
  case base h =>
    dsimp
    have ⟨_, ⟨t', h'⟩⟩ := orig h t
    refine ⟨_, ⟨t', .base _ _ h'⟩⟩
  case trans H h =>
    have ⟨_, ⟨t', h'⟩⟩ := h t
    have ⟨q', ⟨t'', h''⟩⟩ := H t'
    have := TC.trans _ _ _ h'' h'
    exists q'

theorem trans_sim (orig: Bisimulation r): Bisimulation (P:=P) (TC r) :=
  ⟨trans_l_sim orig.left, trans_r_sim orig.right⟩

def Union (r s: α → α → Prop): α → α → Prop := λx y ↦ r x y ∨ s x y

theorem union_l_sim (a: LeftSim r) (b: LeftSim s):
  LeftSim (P:=P) (Union r s) :=
  fun h t => match h with
  | .inl h => have ⟨_, ⟨_, _⟩⟩ := a h t; ⟨_, ⟨‹_›, .inl ‹_›⟩⟩
  | .inr h => have ⟨_, ⟨_, _⟩⟩ := b h t; ⟨_, ⟨‹_›, .inr ‹_›⟩⟩

theorem union_sim (a: Bisimulation r) (b: Bisimulation s): Bisimulation (P:=P) (Union r s) := by
  refine ⟨union_l_sim a.left b.left, ?_⟩
  apply union_l_sim a.right
  exact b.right

theorem Bisimilar.trans {a b c: P}: Bisimilar a b → Bisimilar b c → Bisimilar a c := by
  intro ⟨r, ⟨h, _⟩⟩ ⟨s, ⟨h', _⟩⟩
  exists TC (Union r s)
  have x: TC (Union r s) a b := .base _ _ $ .inl h
  have y: TC (Union r s) b c := .base _ _ $ .inr h'
  refine ⟨.trans _ _ _ x y, trans_sim (union_sim ‹_› ‹_›)⟩

instance [LTS P] : Equivalence (Bisimilar (P:=P)) where
  refl := Bisimilar.refl
  symm := Bisimilar.symm
  trans := Bisimilar.trans

theorem sim_bisim: Bisimulation (Bisimilar (P:=P)) where
  left := by
    intro p p' q a ⟨r, ⟨h, h'⟩⟩ t
    have ⟨_, ⟨t', H⟩⟩ := h'.left h t
    refine ⟨_, ⟨t', ?_⟩⟩
    exists r
  right := by
    intro p p' q a ⟨r, ⟨h, h'⟩⟩ t
    have ⟨_, ⟨t', H⟩⟩ := h'.right h t
    refine ⟨_, ⟨t', ?_⟩⟩
    exists r

structure BisimF (inner: P → P → Prop) (p q: P): Prop where
  left: LTS.transition p a p' → ∃q', (LTS.transition q a q' ∧ inner p' q')
  right: LTS.transition q a q' → ∃p', (LTS.transition p a p' ∧ inner p' q')

theorem bisim_cond_of_bisim: Bisimilar p q → BisimF Bisimilar p q :=
  fun ⟨r, ⟨h, sim⟩⟩ => by
    constructor
    . intro _ _ t
      have ⟨q', ⟨_, _⟩⟩ := sim.left h t
      refine ⟨q', ⟨‹_›, ?_⟩⟩
      exists r
    . intro _ _ t
      have ⟨q', ⟨_, _⟩⟩ := sim.right h t
      refine ⟨q', ⟨‹_›, ?_⟩⟩
      exists r

theorem bisim_cond_l_sim: LeftSim (P:=P) (BisimF Bisimilar) := fun h t =>
  have ⟨q', ⟨_, _⟩⟩ := h.left t
  ⟨q', ⟨‹_›, bisim_cond_of_bisim _ _ ‹_›⟩⟩

theorem bisim_cond_r_sim: RightSim (P:=P) (BisimF Bisimilar) := fun h t =>
  have ⟨q', ⟨_, _⟩⟩ := h.right t
  ⟨q', ⟨‹_›, bisim_cond_of_bisim _ _ ‹_›⟩⟩

-- basically proves `Bisimilar` is a fix point of `BisimF`
theorem bisim_cond: Bisimilar p q ↔ BisimF Bisimilar p q where
  mp := bisim_cond_of_bisim _ _
  mpr := fun _ => by
    exists BisimF Bisimilar
    refine ⟨‹_›, ?_⟩
    refine ⟨bisim_cond_l_sim, bisim_cond_r_sim⟩

theorem bisim_fix: Bisimilar = BisimF Bisimilar (P:=P) := by
  funext
  rw [bisim_cond]

def InductiveProp (F: (α → α → Prop) → (α → α → Prop)): Nat → α → α → Prop
| .zero => fun _ _ => True
| (.succ n) => F (InductiveProp F n)

-- basically Fix (BisimF)
def BisimCondStrong (p q: P) := ∀n, InductiveProp BisimF n p q
