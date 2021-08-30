-- tyring to port ideas from https://arxiv.org/pdf/2107.12144.pdf

import tactic.basic
import tactic.omega
import control.bifunctor
import init.control.monad_fail


universes u v

inductive tree (op_t : Sort u) (leaf_t : Sort v) 
  | leaf (tip : leaf_t) : tree
  | branch (op : op_t) (l r : tree) : tree 

notation ` ⟪` a `⟫ ` := tree.leaf a

def tree.bimap {op leaf leaf' op'} (f : op → op') (g : leaf → leaf') : tree op leaf → tree op' leaf' 
| ⟪l⟫ := tree.leaf (g l)
| (tree.branch op l r) := tree.branch (f op) l.bimap r.bimap

instance : bifunctor tree := {
  bimap := λ {op op' leaf leaf'} (f : op → op') (g : leaf → leaf'), tree.bimap f g
}

lemma tree.id_bimap {op_t : Type u} {leaf_t : Type v} : ∀ x : tree op_t leaf_t, bimap id id x = x
| (tree.leaf l) := rfl
| (tree.branch op l r) := congr_arg2 (tree.branch op) (tree.id_bimap l) (tree.id_bimap r)

lemma tree.bimap_bimap {α₀ α₁ α₂ : Type u} {β₀ β₁ β₂ : Type v}
  (f : α₀ → α₁) (f' : α₁ → α₂) 
  (g : β₀ → β₁) (g' : β₁ → β₂) : ∀ (x : tree α₀ β₀),
    bimap f' g' (bimap f g x) = bimap (f' ∘ f) (g' ∘ g) x 
| (tree.leaf tip) := rfl
| (tree.branch op l r) := 
  congr_arg2 (tree.branch (f' (f op))) (tree.bimap_bimap l) (tree.bimap_bimap r)

instance : is_lawful_bifunctor tree := {
  id_bimap := by {apply tree.id_bimap},
  bimap_bimap := by {apply tree.bimap_bimap}
}

inductive pie_type_op 
  | add
  | mul

instance : decidable_eq pie_type_op
| pie_type_op.add  pie_type_op.add  := is_true rfl
| pie_type_op.add  pie_type_op.mul := is_false (λ hyp, pie_type_op.no_confusion hyp)
| pie_type_op.mul pie_type_op.add  := is_false (λ hyp, pie_type_op.no_confusion hyp)
| pie_type_op.mul pie_type_op.mul := is_true rfl

precedence `:+:` :50
infix ` :+: ` := tree.branch pie_type_op.add 
precedence `:*:` :50
infix ` :*: ` := tree.branch pie_type_op.mul

open pie_type_op

inductive one_zero
  | one
  | zero

instance : decidable_eq one_zero
| one_zero.one  one_zero.one  := is_true rfl
| one_zero.one  one_zero.zero := is_false (λ hyp, one_zero.no_confusion hyp)
| one_zero.zero one_zero.one  := is_false (λ hyp, one_zero.no_confusion hyp)
| one_zero.zero one_zero.zero := is_true rfl

abbreviation pie_type := tree pie_type_op one_zero

instance (leaf : Type) : has_add (tree pie_type_op leaf) := ⟨λ l r, l :+: r⟩ 
instance (leaf : Type) : has_mul (tree pie_type_op leaf) := ⟨λ l r, l :*: r⟩
instance : has_one pie_type := ⟨tree.leaf one_zero.one⟩
instance : has_zero pie_type := ⟨tree.leaf one_zero.zero⟩

def pie_type_fold {α} (zero one : α) (add mul : α → α → α) : pie_type → α
  | 0 := zero
  | 1 := one
  | (l :+: r) := add (pie_type_fold l) (pie_type_fold r)
  | (l :*: r) := mul (pie_type_fold l) (pie_type_fold r)

section

parameter α : Type

parameters zero one : α 

parameters add mul : α → α → α

parameters {α zero one add mul}

local notation `ff` := pie_type_fold zero one add mul

@[simp]lemma pie_type_fold.zero : ff (0 : pie_type) = zero := rfl
@[simp]lemma pie_type_fold.one : ff (1 : pie_type) = one := rfl
@[simp]lemma pie_type_fold.add (l r : pie_type) : ff (l + r) = add (ff l) (ff r) := rfl
@[simp]lemma pie_type_fold.mul (l r : pie_type) : ff (l * r) = mul (ff l) (ff r) := rfl

end

instance tree.decidable_eq (op leaf) [d_op : decidable_eq op] [decidable_eq leaf] : decidable_eq (tree op leaf) 
  | (tree.leaf x) (tree.leaf y) :=
    if h : x = y
      then is_true (congr_arg _ h)
      else is_false (λ hyp, h (tree.leaf.inj_arrow hyp id))
  | (tree.branch xop xl xr) (tree.branch yop yl yr) :=
      match (d_op xop yop, tree.decidable_eq xl yl, tree.decidable_eq xr yr) with
      | (is_true hop, is_true hl, is_true hr) := 
        is_true (congr (congr (congr_arg tree.branch hop) hl) hr)
      | (is_false h, _, _) := is_false ( λ hyp, by refine h (tree.branch.inj_arrow hyp (λ hop _ _, hop)))
      | (_, is_false h, _) := is_false ( λ hyp, by refine h (tree.branch.inj_arrow hyp (λ _ hl  _, hl)))
      | (_, _, is_false h) := is_false ( λ hyp, by refine h (tree.branch.inj_arrow hyp (λ _ _ hr , hr)))
      end
  | (tree.leaf _) (tree.branch _ _ _) := is_false (λ hyp, tree.no_confusion hyp)
  | (tree.branch _ _ _) (tree.leaf _) := is_false (λ hyp, tree.no_confusion hyp)
  
inductive subatomic : Type 
  | id : subatomic
  | swap_add: subatomic
  | zero_add : subatomic
  | assoc_add : subatomic
  | swap_mul: subatomic
  | one_mul : subatomic
  | assoc_mul : subatomic 
  | distrib : subatomic
  | distrib0 : subatomic

open subatomic

inductive subatomic.typed : subatomic → pie_type → pie_type → Type
  | id : ∀ b, subatomic.typed id b b
  | swap_add: ∀ a b : pie_type, subatomic.typed swap_add (a + b) (b + a)
  | zero_add : ∀ a, subatomic.typed zero_add (0 + a) a
  | assoc_add : ∀ a b c, subatomic.typed assoc_add (a + b + c) (a + (b + c))
  | swap_mul: ∀ a b, subatomic.typed swap_mul (a * b) (b * a)
  | one_mul : ∀ a, subatomic.typed one_mul (1 * a) a
  | assoc_mul : ∀ a b c, subatomic.typed assoc_mul (a * b * c) (a * (b * c))
  | distrib : ∀ a b c, subatomic.typed distrib (a * (b + c)) (a * b + a * c)
  | distrib0 : ∀ a, subatomic.typed distrib0 (a * 0) 0

inductive atomic : Type
  | forward : subatomic → atomic
  | backward : subatomic → atomic

open atomic

inductive atomic.typed : atomic → pie_type → pie_type → Type
  | forward {s : subatomic} {A B : pie_type} : s.typed A B → atomic.typed (forward s) A B
  | backward {s : subatomic} {A B : pie_type} : s.typed B A → atomic.typed (backward s) A B

def atomic.inv : atomic → atomic
  | (atomic.forward sa) := atomic.backward sa
  | (atomic.backward sa) := atomic.forward sa

inductive pie_op 
  | comp : pie_op
  | type_op : pie_type_op → pie_op 

abbreviation pie := tree pie_op atomic

precedence `:∘` : 50
infix `:∘` := tree.branch pie_op.comp
precedence `:+` : 50
infix `:+` := tree.branch (pie_op.type_op add)
precedence `:*` : 50
infix `:*` := tree.branch (pie_op.type_op mul)

def tree.inv : pie → pie
  | (tree.leaf atom) := tree.leaf atom.inv
  | (f :∘ g) := g.inv :∘ f.inv
  | (f :+ g) := f.inv :+ g.inv
  | (f :* g) := f.inv :* g.inv

@[simp]
lemma atomic.inv_inv {a : atomic} : a.inv.inv = a := by {
  cases a; unfold atomic.inv,
}

@[simp]
lemma tree.inv_inv : ∀ {p : pie}, p.inv.inv = p 
  | ⟪atom⟫ := congr_arg _ atomic.inv_inv
  | (f :∘ g) := congr_arg2 _ tree.inv_inv tree.inv_inv 
  | (f :+ g) := congr_arg2 _ tree.inv_inv tree.inv_inv 
  | (f :* g) := congr_arg2 _ tree.inv_inv tree.inv_inv

inductive tree.typed : pie → pie_type → pie_type → Type
  | atomic (atom : atomic) {a b} : atom.typed a b → tree.typed ⟪atom⟫ a b
  | comp {a} (b) {c} {left : pie} {right : pie} :
    tree.typed left a b → 
    tree.typed right b c →
    tree.typed (left :∘ right) a c
  | add (a b c d) (f g : pie) : 
    tree.typed f a b →
    tree.typed g c d →
    tree.typed (f :+ g) (a + c) (b + d)
  | mul (a b c d) (f g : pie) : 
    tree.typed f a b →
    tree.typed g c d →
    tree.typed (f :* g) (a * c) (b * d)

section abstract_machine

inductive tree_context (α : Type u) (β : Type v)
  | root : tree_context
  | on_left : ∀ (op : α) (up : tree_context) (right : tree α β), tree_context
  | on_right : ∀ (op : α) (left : tree α β) (up : tree_context), tree_context

open tree_context

notation `pie_context` := tree_context pie_op atomic

def tree_context.plug_in {α β} : tree_context α β → tree α β → tree α β
| root t := t
| (on_left op up right) t := up.plug_in (tree.branch op t right)  
| (on_right op left up) t := up.plug_in (tree.branch op left t)

@[simp]
lemma tree_context.plug_in.root {α β} (t : tree α β) : root.plug_in t = t := rfl 
@[simp]
lemma tree_context.plug_in.on_left {α β} (op : α) (t right : tree α β) (up) : 
  (on_left op up right).plug_in t = up.plug_in (tree.branch op t right) := rfl
@[simp]
lemma tree_context.plug_in.on_right {α β} (op : α) (t left : tree α β) (up) : 
  (on_right op left up).plug_in t = up.plug_in (tree.branch op left t) := rfl

def get_type_at : 
  ∀  (c : pie_context) (p : pie) {A B : pie_type} (t : tree.typed (c.plug_in p) A B),
  Σ A' B', tree.typed p A' B' := by {
    intros c,
    induction c; intros,
    {exact ⟨A, B, t⟩},
    {
      let pie_up := (on_left c_op root c_right).plug_in p,
      have : Σ A' B', typed pie_up A' B' := c_ih pie_up t,
      obtain ⟨A', B', pie_up_typed⟩ := this,
      have : pie_up = tree.branch c_op p c_right := rfl,
      rw this at *,
      clear this pie_up,
      cases pie_up_typed,
      {
        existsi A', 
        existsi pie_up_typed_b,
        assumption,
      },
      all_goals { try {
        existsi pie_up_typed_a, 
        existsi pie_up_typed_b,
        assumption,
      }},
    },
    {
      let pie_up := (on_right c_op c_left root).plug_in p,
      have : Σ A' B', typed pie_up A' B' := c_ih pie_up t,
      obtain ⟨A', B', pie_up_typed⟩ := this,
      have : pie_up = tree.branch c_op c_left p := rfl,
      rw this at *,
      clear this pie_up,
      cases pie_up_typed,
      {
        existsi pie_up_typed_b,
        existsi B', 
        assumption,
      },
      all_goals {
        existsi pie_up_typed_c, 
        existsi pie_up_typed_d,
        assumption,
      },
    }
  }

inductive emptyt

def tree.to_type : pie_type → Type := pie_type_fold emptyt unit (⊕) (×)

instance : has_coe_to_sort pie_type := 
  {
    S := Type,
    coe := tree.to_type
  }

@[simp]lemma pie_type.coe_to_sort.zero : ↥(0 : pie_type) = emptyt := rfl
@[simp]lemma pie_type.coe_to_sort.one : ↥(1 : pie_type) = unit := rfl
@[simp]lemma pie_type.coe_to_sort.add (l r : pie_type) : ↥(l + r) = (↥l ⊕ ↥r) := rfl
@[simp]lemma pie_type.coe_to_sort.mul (l r : pie_type) : ↥(l * r) = (↥l  × ↥r) := rfl
@[simp]lemma pie_type.coe_to_sort.to_to_type (b : pie_type) : b.to_type = ↥b := rfl

structure am_state :=
  (focus_left : pie_type)
  (focus_right : pie_type)
  (focus : pie)
  (focus_typed : typed focus focus_left focus_right)
  (board : pie_context)
  (value : focus_left ⊕ focus_right)

def am_state.typed (state : am_state) : pie_type → pie_type → Type :=
  (state.board.plug_in state.focus).typed

open sum

def assoc_mul_run {A B C : Type} : ((A × B) × C) → (A × (B × C))
  | ((a, b), c) := (a, (b, c))

@[simp]
lemma assoc_mul_run_def {A B C : Type} (a : A) (b : B) (c : C) :
  assoc_mul_run ((a, b), c) = (a, (b, c)) := rfl

def zero_add_run {B : pie_type} : (0 + B) → B
  | (inl z) := z.cases_on (λ _, B)
  | (inr b) := b

@[simp]
lemma zero_add_run.inl (z : (0 : pie_type)) {B} : 
  zero_add_run (inl z : (0 + B : pie_type)) = z.cases_on (λ _, B) := rfl

@[simp]
lemma zero_add_run.inr {B : pie_type} (b : B) : 
  zero_add_run (inr b : (0 + B : pie_type)) = b := rfl

def assoc_add_run {A B C : pie_type} : (A + B + C) → (A + (B + C))
  | (inl (inl a)) := sum.inl a
  | (inl (inr b)) := sum.inr (inl b)
  | (inr c) := sum.inr (inr c)

@[simp]
def assoc_add_run.inl_inl {A B C : pie_type} {a : A} : 
  @assoc_add_run A B C (inl (inl a)) = inl a := rfl

@[simp]
def assoc_add_run.inl_inr {A B C : pie_type} {b : B} : 
  @assoc_add_run A B C (inl (inr b)) = inr (inl b) := rfl

@[simp]
def assoc_add_run.inr {A B C : pie_type} {c : C} : 
  @assoc_add_run A B C (inr c) = inr (inr c) := rfl

def distrib_run {A B C : pie_type} : (A * (B + C)) → A * B + A * C
  | ⟨a, inl b⟩ := inl ⟨a, b⟩
  | ⟨a, inr c⟩ := inr ⟨a, c⟩

@[simp]
def distrib_run.inl {A B C : pie_type} {a : A} {b : B} : 
  @distrib_run A B C ⟨a, inl b⟩ = inl ⟨a, b⟩ := rfl

@[simp]
def distrib_run.inr {A B C : pie_type} {a : A} {c : C} : 
  @distrib_run A B C ⟨a, inr c⟩ = inr ⟨a, c⟩ := rfl

def subatomic.run : ∀ (s : subatomic) {A B : pie_type}, s.typed A B → (A → B)
| subatomic.id := λ A B p, by {cases p, exact id}
| swap_add := λ A B p, by {cases p, exact sum.swap}
| subatomic.zero_add := λ A B p, by {cases p, exact zero_add_run}
| assoc_add := λ A B p, by {cases p, exact assoc_add_run}
| swap_mul := λ A B p, by {cases p, exact prod.swap}
| subatomic.one_mul := λ A B p, by {cases p, exact prod.snd}
| assoc_mul := λ A B p, by {cases p, exact assoc_mul_run}
| subatomic.distrib := λ A B p, by {cases p, exact distrib_run}
| distrib0 := λ A B p, by {cases p, exact prod.snd}

def assoc_mul_backrun {A B C : Type} : (A × B × C) → ((A × B) × C)
  | (a, (b, c)) := ((a, b), c)

@[simp]
lemma assoc_mul_backrun_def {A B C : Type} (a : A) (b : B) (c : C) :
  assoc_mul_backrun (a, (b, c)) = ((a, b), c) := rfl

def assoc_add_backrun {A B C : pie_type} : (A + (B + C)) → (A + B + C)
  | (inl a) := inl (inl a)
  | (inr (inl b)) := inl (inr b)
  | (inr (inr c)) := (inr c)

@[simp]
def assoc_add_backrun.inl {A B C : pie_type} {a : A} : 
  @assoc_add_backrun A B C (inl a) = inl (inl a) := rfl

@[simp]
def assoc_add_backrun.inr_inl {A B C : pie_type} {b : B} : 
  @assoc_add_backrun A B C (inr (inl b)) = inl (inr b) := rfl

@[simp]
def assoc_add_backrun.inr_inr {A B C : pie_type} {c : C} : 
  @assoc_add_backrun A B C (inr (inr c)) = inr c := rfl

def one_mul_backrun {A : pie_type} : A → (1 * A) 
  | a := ⟨(), a⟩

@[simp]
lemma one_mul_backrun.def {A : pie_type} (a : A) : one_mul_backrun a = ⟨(), a⟩ := rfl

def distrib_backrun {A B C : pie_type} : A * B + A * C → A * (B + C)
  | (inl ⟨a, b⟩) := ⟨a, inl b⟩ 
  | (inr ⟨a, c⟩) := ⟨a, inr c⟩

@[simp]
def distrib_backrun.inl {A B C : pie_type} {a : A} {b : B} : 
  @distrib_backrun A B C (inl ⟨a, b⟩) = ⟨a, inl b⟩ := rfl

@[simp]
def distrib_backrun.inr {A B C : pie_type} {a : A} {c : C} : 
  @distrib_backrun A B C (inr ⟨a, c⟩) = ⟨a, inr c⟩ := rfl

def distrib0_backrun (A : pie_type) : (0 : pie_type) → A * 0 
  | z := ⟨z.cases_on (λ _, A), z⟩

@[simp]
def distrib0_backrun.def (A : pie_type) (z : (0 : pie_type)) : 
  distrib0_backrun A z = (⟨z.cases_on (λ _, A), z⟩ : A * 0) := rfl

def subatomic.backrun : ∀ (s : subatomic) {A B : pie_type}, s.typed A B → (B → A)
| subatomic.id := λ A B p, by {cases p, exact id}
| swap_add := λ A B p, by {cases p, exact sum.swap}
| subatomic.zero_add := λ A B p, by {cases p, exact inr}
| assoc_add := λ A B p, by {cases p, exact assoc_add_backrun}
| swap_mul := λ A B p, by {cases p, exact prod.swap}
| subatomic.one_mul := λ A B p, by {cases p, exact one_mul_backrun}
| assoc_mul := λ A B p, by {cases p, exact assoc_mul_backrun}
| subatomic.distrib := λ A B p, by {cases p, exact distrib_backrun}
| distrib0 := λ A B p, by {cases p, exact distrib0_backrun _}

abbreviation tree.card : pie_type → ℕ := pie_type_fold 0 1 (+) (*)

lemma pie_type.ind (P : pie_type → Prop) 
  (on_zero : P 0)
  (on_one : P 1)
  (on_add : ∀ l r, P l → P r → P (l :+: r))
  (on_mul : ∀ l r, P l → P r → P (l :*: r)) : ∀ p, P p
  | 0 := on_zero
  | 1 := on_one
  | (l :+: r) := on_add l r (pie_type.ind l) (pie_type.ind r) 
  | (l :*: r) := on_mul l r (pie_type.ind l) (pie_type.ind r) 

def pie_type.rec (P : pie_type → Type u) 
  (on_zero : P 0)
  (on_one : P 1)
  (on_add : ∀ l r, P l → P r → P (l :+: r))
  (on_mul : ∀ l r, P l → P r → P (l :*: r)) : ∀ p, P p
  | 0 := on_zero
  | 1 := on_one
  | (l :+: r) := on_add l r (pie_type.rec l) (pie_type.rec r) 
  | (l :*: r) := on_mul l r (pie_type.rec l) (pie_type.rec r)

def pie_type.ind_on (p : pie_type) {P : pie_type → Prop} 
  (on_zero on_one on_add on_mul) : P p :=
  pie_type.ind P on_zero on_one on_add on_mul p

def pie_type.rec_on (p : pie_type) {P : pie_type → Type u} 
  (on_zero on_one on_add on_mul) : P p :=
  pie_type.rec P on_zero on_one on_add on_mul p

def fin.index : ∀ {n m : ℕ}, fin n → fin m → (fin (n * m))
  | 0 m i j := false.rec (fin (0 * m)) (nat.not_lt_zero i.val i.prop)
  | n 0 i j := false.rec (fin (n * 0)) (nat.not_lt_zero j.val j.prop)
  | (n + 1) (m + 1) i j :=
    ⟨i.val * (m + 1) + j.val, by {
      calc i.val * (m + 1) + j.val < i.val * (m + 1) + (m + 1) : by {apply nat.add_lt_add_left j.prop}
      ... = i.val * (m + 1) + 1 * (m + 1) : by {ring_nf}
      ... = (i.val + 1) * (m + 1) : by {ring}
      ... ≤ (n + 1) * (m + 1) : 
        nat.mul_le_mul (nat.add_le_add_right (nat.lt_succ_iff.mp i.prop) 1) (le_refl _)
    }⟩

lemma fin.unindex.aux : ∀ k j x : nat, 0 < j → (k < j * x → k/j < x) := by {
  intros k j x h,
  cases j,
  {cases h},
  clear h, intros mul_hyp,
  exact nat.div_lt_of_lt_mul mul_hyp
}

lemma fin.unindex.aux2 : ∀ i m, m > 0 → (i % m) < m := by {
  intros,
  exact nat.mod_lt i ᾰ
}

def fin.unindex : ∀ {n m : ℕ}, (fin (n * m)) → fin n × fin m
  | 0 m i := by {rw zero_mul at i, apply fin_zero_elim i}
  | n 0 i := by {rw mul_zero at i, apply fin_zero_elim i}
  | (n + 1) (m + 1) i := 
    ⟨
      ⟨
        i.val / (m + 1), by {
          obtain ⟨i_val, i_prop⟩ := i,
          simp,
          apply nat.div_lt_of_lt_mul,
          rw mul_comm,
          exact i_prop,
        }
      ⟩, 
      ⟨(i.val % (m + 1)), i.val.mod_lt (nat.succ_pos m)⟩
    ⟩

open function

lemma fin.index_equiv.aux (m x y : ℕ)
  (yh : y < m)
  (h : 0 < m) :
  (x * m + y) / m = x := by {
  rw add_comm,
  rw nat.add_mul_div_right,
  rw nat.div_eq_of_lt,
  apply nat.zero_add,
  all_goals{assumption},
}

def fin.index_equiv {n m} : equiv (fin n × fin m) (fin (n * m)) :=
  {
    to_fun := uncurry fin.index,
    inv_fun := fin.unindex,
    left_inv := by {
      intros x,
      obtain ⟨x, y⟩ := x,
      cases n,
      {exact fin_zero_elim x},
      cases m,
      {exact fin_zero_elim y},
      obtain ⟨x, xh⟩ := x,
      obtain ⟨y, yh⟩ := y,
      unfold uncurry fin.index fin.unindex,
      simp,
      split,
      have : m.succ = (m + 1) := rfl,
      simp_rw this at *,
      clear this,
      have : 0 < m + 1 := nat.succ_pos m,
      apply fin.index_equiv.aux; assumption,
      rw add_comm,
      rw nat.add_mul_mod_self_right,
      apply nat.mod_eq_of_lt,
      exact yh,
    },
    right_inv := by {
      intros x,
      cases n,
      {rw zero_mul at x, exact fin_zero_elim x},
      cases m,
      {rw mul_zero at x, apply fin_zero_elim x},
      obtain ⟨x, xh⟩ := x,
      unfold uncurry fin.index fin.unindex,
      simp,
      rw mul_comm,
      rw add_comm,
      apply nat.mod_add_div,
    }
  }

lemma fin.index_bijective {n m} : bijective (uncurry fin.index : (fin n × fin m) → fin (n * m)) := by {
  have : uncurry fin.index = (fin.index_equiv : (fin n × fin m) → fin (n * m)) := rfl,
  rw this,
  apply equiv.bijective
}

def pie_type_to_fin : ∀ (A : pie_type) (v : A), fin (A.card)
  | 0 e := e.cases_on _
  | 1 () := ⟨0, zero_lt_one⟩
  | (l :+: r) (inl v) :=
    fin.cast_add (r.card) (pie_type_to_fin _ v)
  | (l :+: r) (inr v) :=
    fin.nat_add (l.card) (pie_type_to_fin _ v)
  | (l :*: r) (vl, vr) := (pie_type_to_fin _ vl).index (pie_type_to_fin _ vr)

lemma pie_type_to_fin.on_pair {l vl r vr} : pie_type_to_fin (l :*: r) (vl, vr) = (pie_type_to_fin _ vl).index (pie_type_to_fin _ vr) := rfl

lemma pie_type_to_fin_injective.aux {l r} (x y) : 
  pie_type_to_fin (l :+: r) (inl x) ≠ pie_type_to_fin (l :+: r) (inr y) := by
    {
      apply ne_of_lt,
      unfold pie_type_to_fin,
      unfold fin.cast_add fin.nat_add fin.cast_le,
      simp_rw order_embedding.coe_of_strict_mono,
      unfold fin.cast_lt,
      simp,
      unfold_coes,
      calc (pie_type_to_fin l x).val < tree.card l : (pie_type_to_fin l x).prop
      ... ≤ tree.card l + (pie_type_to_fin r y).val : _,
      exact le_self_add,
    }

example {α β} (f : α → β) : bijective f → injective f := by {intros, refine bijective.injective ᾰ}

lemma pie_type_to_fin_injective {A} : function.injective (pie_type_to_fin A) := by {
  apply pie_type.ind_on A,
  {
    intros x,
    cases x,
  },
  {
    intros x y _,
    cases x; cases y,
    refl,
  },
  {
    intros l r l_ih r_ih x y x_eq_y,
    cases x; cases y,
    all_goals {try {
      congr,
      unfold pie_type_to_fin at x_eq_y,
      simp at x_eq_y,
    }},
    exact l_ih x_eq_y,
    {
      dedup,
      exfalso,
      revert x_eq_y,
      show pie_type_to_fin (l :+: r) (inl x) ≠ pie_type_to_fin (l :+: r) (inr y),
      apply pie_type_to_fin_injective.aux x y,
    },
    {
      dedup,
      exfalso,
      revert x_eq_y,
      show pie_type_to_fin (l :+: r) (inr x) ≠ pie_type_to_fin (l :+: r) (inl y),
      symmetry,
      apply pie_type_to_fin_injective.aux y x,
    },
    exact r_ih x_eq_y,
  },
  {
    intros l r l_ih r_ih x y fx_eq_fy,
    obtain ⟨xₗ, xᵣ⟩ := x,
    obtain ⟨yₗ, yᵣ⟩ := y,
    simp_rw pie_type_to_fin.on_pair at fx_eq_fy,
    have : ∀ (x : fin (l.card)) (y : fin (r.card)), uncurry fin.index (x,y) = x.index y := λ _ _, rfl,
    simp_rw ← this at fx_eq_fy; clear this,
    have : injective (uncurry fin.index : fin l.card × fin r.card → fin (l.card * r.card))
      := fin.index_bijective.injective,
    unfold injective at this,
    have pre_induction : 
      (pie_type_to_fin _ xₗ, pie_type_to_fin _ xᵣ) = (pie_type_to_fin _ yₗ, pie_type_to_fin _ yᵣ) :=
      this fx_eq_fy,
    clear this fx_eq_fy,
    rw prod.ext_iff at pre_induction,
    congr,
    simp at *,
    apply l_ih pre_induction.1,
    apply r_ih pre_induction.2,
  }
}

@[simp]
lemma sum.swap_inl {α β} {a : α} : (sum.inl a : α ⊕ β).swap = inr a := rfl
@[simp]
lemma sum.swap_inr {α β} {b : β} : (sum.inr b : α ⊕ β).swap = inl b := rfl

@[simp]
lemma prod.swap_def {α β} (a : α) (b : β) : (⟨a,b⟩ : α × β).swap = ⟨b,a⟩ := rfl 

instance pie_type.one.subsingleton : subsingleton (1 : pie_type) := punit.subsingleton

def subatomic.run' : ∀ (s : subatomic) {A B}, s.typed A B → (A ≃ B) :=
  λ s A B p, ⟨s.run p, s.backrun p, by {
    intros a,
    cases p; unfold subatomic.run subatomic.backrun,
    {simp_rw id.def},
    {cases a; simp},
    {cases a, cases a, simp},
    {cases a, cases a, all_goals {simp}},
    {cases a; simp},
    {cases a; cases a_fst, refl},
    {cases a, cases a_fst, simp},
    {cases a, cases a_snd, 
      {rw distrib_run.inl, rw distrib_backrun.inl}, 
      {rw distrib_run.inr, rw distrib_backrun.inr}, 
    },
    {cases a, cases a_snd}
  },
  by {
    intros a,
    cases p; unfold subatomic.run subatomic.backrun,
    {simp_rw id.def},
    {cases a; simp},
    {simp},
    {cases a, simp, cases a; simp},
    {cases a; simp},
    {simp},
    {cases a, cases a_snd, simp},
    {cases a, cases a, 
      {rw distrib_backrun.inl, rw distrib_run.inl}, 
      {cases a, rw distrib_backrun.inr, rw distrib_run.inr}
    },
    {cases a}
  }
  ⟩

#check typed.atomic

def atomic.typed.run {A B : pie_type} : ∀ {a : atomic}, a.typed A B → A ≃ B
| (atomic.forward s) p :=  by {cases p, apply s.run', assumption}
| (atomic.backward s) p := by {cases p, symmetry, apply s.run'; assumption}

def function.on_sum {A B C D} (f : A → B) (g : C → D) : (A ⊕ C) → (B ⊕ D) 
  | (inl l) := (inl (f l))
  | (inr r) := (inr (g r))

@[simp]
lemma function.on_sum.inl {A B C D} (f : A → B) (g : C → D) (l : A) : 
  function.on_sum f g (inl l) = inl (f l) := rfl 

@[simp]
lemma function.on_sum.inr {A B C D} (f : A → B) (g : C → D) (r : C) : 
  function.on_sum f g (inr r) = inr (g r) := rfl

def equiv.on_sum {A B C D} (f : A ≃ B) (g : C ≃ D) : (A ⊕ C) ≃ (B ⊕ D) :=
  {
    to_fun := function.on_sum f.to_fun g.to_fun,
    inv_fun := function.on_sum f.inv_fun g.inv_fun,
    left_inv := by {
      intros x,
      cases x,
      {
        rw function.on_sum.inl,
        rw function.on_sum.inl,
        rw f.left_inv,
      },
      {
        rw function.on_sum.inr,
        rw function.on_sum.inr,
        rw g.left_inv,
      }
    },
    right_inv := by {
      intros x,
      cases x,
      {
        rw function.on_sum.inl,
        rw function.on_sum.inl,
        rw f.right_inv,
      },
      {
        rw function.on_sum.inr,
        rw function.on_sum.inr,
        rw g.right_inv,
      }
    },
  }

def equiv.on_prod {A B C D} (f : A ≃ B) (g : C ≃ D) : (A × C) ≃ (B × D) := {
  to_fun := λ x, prod.mk (f x.1) (g x.2),
  inv_fun := λ x, prod.mk (f.inv_fun x.1) (g.inv_fun x.2),
  left_inv := by {intros x, simp},
  right_inv := by {intros x, simp},
}

def tree.typed.run : ∀ {A B : pie_type} {p : pie}, typed p A B → A ≃ B
  | A B ⟪a⟫ (typed.atomic .(a) a_typed) := a_typed.run
  | A C (f :∘ g) (typed.comp B f_typed g_typed) := f_typed.run.trans g_typed.run
  | (A :+: C) (B :+: D) (f :+ g) (typed.add _ _ _ _ .(f) .(g) f_typed g_typed) :=
    f_typed.run.on_sum g_typed.run
  | (A :*: C) (B :*: D) (f :* g) (typed.mul _ _ _ _ .(f) .(g) f_typed g_typed) :=
    f_typed.run.on_prod g_typed.run

end abstract_machine

