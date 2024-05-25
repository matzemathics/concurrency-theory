import CtLean.Basic

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

instance [Konst N K] : LTS (CCS N K) where
  Act := Act N
  transition := @Transition N K _

variable [Konst N K] (p q: CCS N K)

theorem bisim_choice: Bisimilar p q → Bisimilar p (CCS.choice p q) := by
  intros
  constructor
  sorry
  sorry
