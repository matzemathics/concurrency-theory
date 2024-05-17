
inductive Act (names: Type) where
| name (_: names)
| coname (_: names)
| tau

inductive CCS (N: Type) (K: Type): Type
| nil
| pref (act: Act N) (p: CCS N K)
| par (left: CCS N K) (right: CCS N K)
| choice (left: CCS N K) (right: CCS N K)
| abst (var: N) (p: CCS N K)
| const (k: K)

class Konst (N: Type) (K: Type) where
  acts (k: K): Act N -> Prop
  resolve (k: K): (a: Act N) → acts k a → CCS N K

inductive Complementary: Act N → Act N → Prop
| left: Complementary (.name n) (.coname n)
| right: Complementary (.coname n) (.name n)

class LTS (P: Type) where
  Act: Type
  transition: P → Act → P → Prop

inductive Transition [kdef: Konst N K]: CCS N K -> Act N -> CCS N K -> Prop
| Pre: Transition (.pref a p) a p
| ParL (h: Transition p a p'): Transition (.par p q) a (.par p' q)
| ParR (h: Transition q a q'): Transition (.par p q) a (.par p q')
| Com
  (l: Transition p a p')
  (r: Transition q a' q')
  (_: Complementary a a'):
  Transition (.par p q) .tau (.par p' q')
| SumL (h: Transition p a p'): Transition (.choice p q) a p'
| SumR (h: Transition q a q'): Transition (.choice p q) a q'
| Res
  (h: Transition p a p')
  (not_name: a ≠ .name n)
  (not_coname: a ≠ .coname n):
  Transition (.abst n p) a (.abst n q)
| Rec
  (h: kdef.acts k a)
  (r: p = kdef.resolve k a h):
  Transition (.const k) a p

def Outgoing [LTS P] (p: P) (a: LTS.Act P): Prop :=
  ∃p', LTS.transition p a p'

def Simulate [LTS P] (p q: P) (map: P → P): Nat → Prop
| 0 => True
| .succ n => ∀a, ∀{p': P}, LTS.transition p a p' →
  (LTS.transition q a (map p') ∧ Simulate p' (map p') map n)

structure Bisimulation [LTS P] (p q: P) where
  left_sim: P → P
  right_sim: P → P
  bij_left: ∀p, left_sim (right_sim p) = p
  bij_right: ∀p, right_sim (left_sim p) = p
  coind_left: ∀n, Simulate p q left_sim n
  coind_right: ∀n, Simulate q p right_sim n

def Bisimilar [LTS P] (p q: P) := Nonempty (Bisimulation p q)

structure BisimCond [LTS P] (p q: P): Prop where
  left: ∀{a}, LTS.transition p a p' → ∃q', (LTS.transition q a q' ∧ Bisimilar p' q')
  right: ∀{a}, LTS.transition q a q' → ∃p', (LTS.transition p a p' ∧ Bisimilar p' q')

theorem show_cond [LTS P] (p q: P): Bisimilar p q → BisimCond p q := by
  intro ⟨left_sim, right_sim, bij_left, bij_right, coind_left, coind_right⟩
  constructor
  . intro p' a t
    exists (left_sim p')
    constructor
    . exact (coind_left 1 a t).left
    . refine ⟨left_sim, right_sim, bij_left, bij_right, ?_, ?_⟩
      intro n
      refine (coind_left n.succ a t).right
      intro n
      have t' := (coind_left n.succ a t).left
      have := bij_right _ ▸ (coind_right n.succ a t').right
      refine this
  . intro q' a t
    exists (right_sim q')
    constructor
    . exact (coind_right 1 a t).left
    . refine ⟨left_sim, right_sim, bij_left, bij_right, ?_, ?_⟩
      intro n
      have t' := (coind_right n.succ a t).left
      have := bij_left _ ▸ (coind_left n.succ a t').right
      refine this
      intro n
      refine (coind_right n.succ a t).right

def SelfSim [LTS P] (p: P): Bisimulation p p where
  left_sim := id
  right_sim := id
  bij_left _ := rfl
  bij_right _ := rfl
  coind_left n := by
    induction n generalizing p with
    | zero => trivial
    | succ n ih => refine fun _ _ t => ⟨t, ih _⟩
  coind_right n := by
    induction n generalizing p with
    | zero => trivial
    | succ n ih => refine fun _ _ t => ⟨t, ih _⟩

theorem Bisimilar.refl [LTS P] (p: P): Bisimilar p p :=
  ⟨SelfSim p⟩

instance [Konst N K] : LTS (CCS N K) where
  Act := Act N
  transition := @Transition N K _
