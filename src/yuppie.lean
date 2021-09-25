-- tyring to port ideas from https://arxiv.org/pdf/2107.12144.pdf

import tactic.basic
import tactic.omega

inductive base : Type 
  | zero : base
  | one : base
  | add : base -> base -> base
  | mul : base -> base -> base

instance : has_one base := ⟨base.one⟩
@[simp] 
lemma base.one_is_one : base.one = 1 := rfl

instance : has_zero base := ⟨base.zero⟩ 
@[simp] 
lemma base.zero_is_zero : base.zero = 0 := rfl

instance : has_add base := ⟨base.add⟩

@[simp] 
lemma base.add_is_add {A B : base} : A.add B = A + B := rfl

instance : has_mul base := ⟨base.mul⟩

@[simp] 
lemma base.mul_is_mul {A B : base} : A.mul B = A * B := rfl

open base
instance : decidable_eq base := by {
  intros x,
  induction x with x₀ x₁ x₀_ih x₁_ih x₀ x₁ x₀_ih x₁_ih
    ; intro y; cases y with y₀ y₁ y₀ y₁,
  all_goals {try {right, refl}},
  all_goals {try {left, cc}},
  all_goals {
    have x₀_ih_y₀ := x₀_ih y₀,
    cases x₀_ih_y₀,
    {left, intros h, injection h, apply x₀_ih_y₀, assumption},
    have x₁_ih_y₁ := x₁_ih y₁,
    cases x₁_ih_y₁,
    {left, intros h, injection h, apply x₁_ih_y₁, assumption},
    rw [x₁_ih_y₁, x₀_ih_y₀],
    right, refl,
  }
}

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

inductive subatomic.typed : subatomic → base → base → Type
  | id : ∀ b, subatomic.typed id b b
  | swap_add: ∀ a b : base, subatomic.typed swap_add (a + b) (b + a)
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

inductive atomic.typed : atomic → base → base → Type
  | forward {s : subatomic} {A B : base} : s.typed A B → atomic.typed (forward s) A B
  | backward {s : subatomic} {A B : base} : s.typed B A → atomic.typed (backward s) A B

def atomic.inv : atomic → atomic
  | (atomic.forward sa) := atomic.backward sa
  | (atomic.backward sa) := atomic.forward sa

inductive pie : Type
  | atomic : atomic → pie
  | comp_list : pie → list pie → pie → pie
  | add :  pie → pie → pie
  | mul :  pie → pie → pie

def pie.left (x : pie) : pie :=
  match x with
  | (pie.comp_list l _ _) := l
  | _ := x
  end

def pie.right : pie → pie
  | (pie.comp_list _ _ r) := r
  | x := x

def pie.lefts : pie → list pie
  | (pie.comp_list _ ls r) := ls ++ [r]
  | _ := list.nil

def pie.rights : pie → list pie
  | (pie.comp_list l rs _) := l :: rs
  | _ := list.nil

def pie.comp (x y : pie) : pie := 
  pie.comp_list x.left (x.lefts ++ y.rights) y.right

mutual def pie.inv , list.inv
  with pie.inv : pie → pie
  | (pie.atomic atom) := pie.atomic atom.inv
  | (pie.comp_list left (xs : list pie) right) := pie.comp_list right.inv xs.inv.reverse left.inv
  | (pie.add f g) := f.inv.add g.inv
  | (pie.mul f g) := f.inv.mul g.inv
  with list.inv : list pie → list pie
    | list.nil := list.nil
    | (x :: xs) := x.inv :: xs.inv

@[simp]
lemma list.inv_nil : [].inv = ([] : list pie) := by {unfold list.inv}

@[simp]
lemma list.inv_cons (x : pie) (xs : list pie) : (x::xs).inv = (x.inv :: xs.inv) := by {unfold list.inv}

@[simp]
lemma list.inv_append (l₀ l₁ : list pie) : (l₀ ++ l₁).inv = l₀.inv ++ l₁.inv := by {
  induction l₀; simp,
  apply l₀_ih,
}

@[simp]
lemma atomic.inv_inv {a : atomic} : a.inv.inv = a := by {
  cases a; unfold atomic.inv,
} 

@[simp]
mutual lemma pie.inv_inv, list.inv_inv
  with pie.inv_inv : ∀ {p : pie}, p.inv.inv = p 
  | (pie.atomic atom) := by {unfold pie.inv, congr, exact atomic.inv_inv}
  | (pie.add l r) := by {unfold pie.inv, congr; exact pie.inv_inv}
  | (pie.mul l r) := by {unfold pie.inv, congr; exact pie.inv_inv}
  | (pie.comp_list left xs right) :=by {
    unfold pie.inv, 
    simp_rw pie.inv_inv, 
    split,
    refl,
    split,
    have : ∀ l : list pie, l.inv.reverse = l.reverse.inv := by {
      clear_except,
      intros l,
      induction l,
      rw list.reverse_nil,
      have : list.nil.inv = list.nil := by {unfold list.inv},
      simp_rw this,
      {simp},
      simp,
      congr,
      exact l_ih,
    },
    rw this,
    rw list.reverse_reverse,
    exact list.inv_inv,
    refl,
  }
  with list.inv_inv : ∀ {xs : list pie}, xs.inv.inv = xs
  | [] := by {simp}
  | (x :: xs) := by {simp; split, exact pie.inv_inv, exact list.inv_inv}

mutual inductive pie.typed, list.typed
  with pie.typed : pie → base → base → Type
  | atomic (atom : atomic) {a b} : atom.typed a b → pie.typed (pie.atomic atom) a b
  | comp_list (a b c d) {left : pie} {xs : list pie} {right : pie} :
    pie.typed left a b → 
    list.typed xs b c →
    pie.typed right c d →
    pie.typed (pie.comp_list left xs right) a d
  | add (a b c d) (f g : pie) : 
    pie.typed f a b →
    pie.typed g c d →
    pie.typed (f.add g) (a + c) (b + d)
  | mul (a b c d) (f g : pie) : 
    pie.typed f a b →
    pie.typed g c d →
    pie.typed (f.mul g) (a * c) (b * d)

  with list.typed : list pie → base → base → Type
  | nil (a) : list.typed [] a a
  | cons {a b c} (x : pie) (xs : list pie) :
    pie.typed x a b →
    list.typed xs b c →
    list.typed (x :: xs) a c

lemma list.typed.append {xs ys : list pie} 
  {a b : base} (x_hyp : list.typed xs a b) 
  {c : base} (y_hyp : list.typed ys b c) :
  list.typed (xs ++ ys) a c := by {
    induction x_hyp with b₀ b₁ b₂ b₃ x xs x_hyp xs_hyp ih,
    exact y_hyp,
    exact list.typed.cons x (xs ++ ys) x_hyp (ih y_hyp)
  }

lemma list.typed.singleton {p : pie} {a b} : p.typed a b → list.typed [p] a b :=
  λ h, list.typed.cons p [] h (list.typed.nil _)

lemma pie.comp_typed (f : pie) {a b c : base} :
  (f.typed a b) → 
  ∀ g : pie,
  (g.typed b c) → 
  ((f.comp g).typed a c) := by {
    intros f_hyp g g_hyp,
    cases f_hyp with 
        f b' c' f_hyp
        f_a f_b f_c f_d f_left f_list f_right f_left_h f_list_h f_right_h 
        f_a f_b f_c f_d f_left f_right f_left_h f_right_h  
        f_a f_b f_c f_d f_left f_right f_left_h f_right_h; 
      unfold pie.comp pie.left pie.lefts,
    {
      cases f_hyp with f_s _ _ f_s_hyp,
      all_goals {
        rw list.nil_append,
        cases g_hyp with 
          g_atom g_a g_b g_hyp 
          g_a g_b g_c g_d g_left g_list g_right g_left_h g_list_h g_right_h
          g_a g_b g_c g_d gf gg gf_h gg_h
          g_a g_b g_c g_d gf gg gf_h gg_h;
          unfold pie.rights; unfold pie.right,
        all_goals {
          apply pie.typed.comp_list,
          {apply pie.typed.atomic, constructor, assumption},
        },
        all_goals{ try {apply list.typed.nil}},
        {
          cases g_hyp with s _ _ s_hyp,
          {apply pie.typed.atomic, apply atomic.typed.forward, assumption},
          {apply pie.typed.atomic, apply atomic.typed.backward, assumption},
        },
        apply list.typed.cons; assumption,
        exact g_right_h,
        apply typed.add; assumption,
        apply typed.mul; assumption,
      },
    },
    {
      have f_list_right_h : (f_list ++ [f_right]).typed f_b b,
      {
        apply list.typed.append,
        exact f_list_h,
        apply list.typed.singleton,
        exact f_right_h,
      },
      cases g_hyp with 
        g_atom g_a g_b g_hyp 
        g_a g_b g_c g_d g_left g_list g_right g_left_h g_list_h g_right_h
        g_a g_b g_c g_d gf gg gf_h gg_h
        g_a g_b g_c g_d gf gg gf_h gg_h;
        unfold pie.rights; unfold pie.right,
      all_goals { try{
        rw list.append_nil,
        apply typed.comp_list; try {assumption},
      }},
      exact pie.typed.atomic g_atom g_hyp,
      {
        apply typed.comp_list; try {assumption},
        apply list.typed.append,
        exact f_list_right_h,
        apply list.typed.cons; assumption,
      },
      exact typed.add g_a g_b g_c g_d gf gg gf_h gg_h,
      exact typed.mul g_a g_b g_c g_d gf gg gf_h gg_h,
    },
    all_goals {
      rw list.nil_append,
      cases g_hyp with 
        g_atom g_a g_b g_atom_h
        g_a g_b g_c g_d g_left g_list g_right g_left_h g_list_h g_right_h
        g_a g_b g_c g_d gf gg gf_h gg_h
        g_a g_b g_c g_d gf gg gf_h gg_h;
        unfold pie.rights; unfold pie.right,
      all_goals {
        apply typed.comp_list,
        constructor; assumption,
      },
      all_goals {try {apply typed.nil}},
      exact pie.typed.atomic g_atom g_atom_h,
      apply typed.cons; assumption,
      assumption,
      constructor; assumption,
    },
  }

def T (α) := option (α × α)

def T.map {α β} : T α → (α → β) → T β
  | none _ := none
  | (some (left, right)) f := some (f left, f right)

instance : functor T := {map := λ α β (f : α → β) (x : T α), x.map f}

instance : applicative T :=
  {
    pure := λ α x, some (x, x),
    seq := λ α β tf tx, 
      match tf, tx with
      | (some (f, g)), (some (a, b)) := some (f a, g b)
      | _, _ := none 
      end
  }

section abstract_machine

inductive pie_context : Type
  | add_left : pie → pie_context
  | mul_left : pie → pie_context
  | add_right : pie → pie_context
  | mul_right : pie → pie_context
  | comp_left : list pie → pie → pie_context
  | comp_list : pie → list pie → list pie → pie → pie_context
  | comp_right : pie → list pie → pie_context

open pie_context

def plug_in : pie_context → pie → pie 
| (add_left right) left := pie.add left right
| (mul_left right) left := pie.mul left right
| (add_right left) right := pie.add left right
| (mul_right left) right := pie.mul left right
| (comp_left list right) left := pie.comp_list left list right
| (comp_list left list_left list_right right) mid := 
  pie.comp_list left (list_left ++ [mid] ++ list_right) right
| (comp_right left list) right := pie.comp_list left list right

@[simp] 
lemma plug_in.add_left (left right) : 
  plug_in (add_left right) left = pie.add left right := 
  rfl

@[simp] 
lemma plug_in.mul_left (left right) : 
  plug_in (mul_left right) left = pie.mul left right := 
  rfl

@[simp] 
lemma plug_in.add_right (left right) : 
  plug_in (add_right left) right = pie.add left right := 
  rfl

@[simp] 
lemma plug_in.mul_right (left right) : 
  plug_in (mul_right left) right = pie.mul left right := 
  rfl

@[simp] 
lemma plug_in.comp_left (left list right) : 
  plug_in (comp_left list right) left = pie.comp_list left list right := 
  rfl

@[simp] 
lemma plug_in.comp_list (left list_left mid list_right right) 
  : plug_in (comp_list left list_left list_right right) mid = 
    pie.comp_list left (list_left ++ [mid] ++ list_right) right := rfl

@[simp] 
lemma plug_in.comp_right (left list right) : plug_in (comp_right left list) right = pie.comp_list left list right := 
  rfl

def list.typed.append_midtype {C right} : ∀ {A} {left}, 
  list.typed (left ++ right) A C → 
  Σ B : base, list.typed left A B × list.typed right B C 
  | A [] p := ⟨A, ⟨typed.nil _, by {rw list.nil_append at p, exact p}⟩⟩
  | A (x :: xs) (typed.cons .(x) .(xs ++ right) x_typed xs_right_typed) :=
    match list.typed.append_midtype xs_right_typed with
    | ⟨B, p⟩ := ⟨B, ⟨typed.cons x xs x_typed p.1, p.2⟩ ⟩
    end

mutual def pie.depth, list.depth
  with pie.depth : pie -> ℕ
  | (pie.atomic atom) := 1
  | (pie.add l r) := (max l.depth r.depth) + 1
  | (pie.mul l r) := (max l.depth r.depth) + 1
  | (pie.comp_list left list_pie right) := (max left.depth (max list_pie.depth right.depth)) + 1
  with list.depth : list pie → ℕ 
  | [] := 1
  | (x :: xs) := (x.depth + xs.depth) + 1

inductive emptyt

def base.to_type : base → Type
  | base.zero := emptyt
  | base.one := unit
  | (base.add l r) := l.to_type ⊕ r.to_type
  | (base.mul l r) := l.to_type  × r.to_type

@[simp]lemma base.to_type.zero : (0:base).to_type = emptyt := rfl
@[simp]lemma base.to_type.one : (1:base).to_type = unit := rfl
@[simp]lemma base.to_type.add (l r : base) : (l + r).to_type = (l.to_type ⊕ r.to_type) := rfl
@[simp]lemma base.to_type.mul (l r : base) : (l * r).to_type = (l.to_type  × r.to_type) := rfl

instance : has_coe_to_sort base := 
  {
    S := Type,
    coe := base.to_type
  }

@[simp]lemma base.coe_to_sort.zero : ↥(base.zero) = emptyt := rfl
@[simp]lemma base.coe_to_sort.one : ↥(base.one) = unit := rfl
@[simp]lemma base.coe_to_sort.add (l r : base) : ↥(l + r) = (↥l ⊕ ↥r) := rfl
@[simp]lemma base.coe_to_sort.mul (l r : base) : ↥(l * r) = (↥l  × ↥r) := rfl
@[simp]lemma base.coe_to_sort.to_to_type (b : base) : b.to_type = ↥b := rfl

def list.plug_in : pie → list pie_context → pie :=
  (list.foldl (flip plug_in))

structure am_state :=
  (focus_left : base)
  (focus_right : base)
  (focus : pie)
  (focus_typed : focus.typed focus_left focus_right)
  (board : list pie_context)
  (value : focus_left ⊕ focus_right)

def am_state.typed (state : am_state) : base → base → Type :=
  (state.board.plug_in state.focus).typed

open sum

def assoc_mul_run {A B C : Type} : ((A × B) × C) → (A × (B × C))
  | ((a, b), c) := (a, (b, c))

@[simp]
lemma assoc_mul_run_def {A B C : Type} (a : A) (b : B) (c : C) :
  assoc_mul_run ((a, b), c) = (a, (b, c)) := rfl

def zero_add_run {B : base} : (0 + B) → B
  | (inl z) := z.cases_on (λ _, B)
  | (inr b) := b

@[simp]
lemma zero_add_run.inl (z : (0 : base)) {B} : 
  zero_add_run (inl z : (0 + B : base)) = z.cases_on (λ _, B) := rfl

@[simp]
lemma zero_add_run.inr {B : base} (b : B) : 
  zero_add_run (inr b : (0 + B : base)) = b := rfl

def assoc_add_run {A B C : base} : (A + B + C) → (A + (B + C))
  | (inl (inl a)) := sum.inl a
  | (inl (inr b)) := sum.inr (inl b)
  | (inr c) := sum.inr (inr c)

@[simp]
def assoc_add_run.inl_inl {A B C : base} {a : A} : 
  @assoc_add_run A B C (inl (inl a)) = inl a := rfl

@[simp]
def assoc_add_run.inl_inr {A B C : base} {b : B} : 
  @assoc_add_run A B C (inl (inr b)) = inr (inl b) := rfl

@[simp]
def assoc_add_run.inr {A B C : base} {c : C} : 
  @assoc_add_run A B C (inr c) = inr (inr c) := rfl

def distrib_run {A B C : base} : (A * (B + C)) → A * B + A * C
  | ⟨a, inl b⟩ := inl ⟨a, b⟩
  | ⟨a, inr c⟩ := inr ⟨a, c⟩

@[simp]
def distrib_run.inl {A B C : base} {a : A} {b : B} : 
  @distrib_run A B C ⟨a, inl b⟩ = inl ⟨a, b⟩ := rfl

@[simp]
def distrib_run.inr {A B C : base} {a : A} {c : C} : 
  @distrib_run A B C ⟨a, inr c⟩ = inr ⟨a, c⟩ := rfl

def subatomic.run : ∀ (s : subatomic) {A B : base}, s.typed A B → (A → B)
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

def assoc_add_backrun {A B C : base} : (A + (B + C)) → (A + B + C)
  | (inl a) := inl (inl a)
  | (inr (inl b)) := inl (inr b)
  | (inr (inr c)) := (inr c)

@[simp]
def assoc_add_backrun.inl {A B C : base} {a : A} : 
  @assoc_add_backrun A B C (inl a) = inl (inl a) := rfl

@[simp]
def assoc_add_backrun.inr_inl {A B C : base} {b : B} : 
  @assoc_add_backrun A B C (inr (inl b)) = inl (inr b) := rfl

@[simp]
def assoc_add_backrun.inr_inr {A B C : base} {c : C} : 
  @assoc_add_backrun A B C (inr (inr c)) = inr c := rfl

def one_mul_backrun {A : base} : A → (1 * A) 
  | a := ⟨(), a⟩

@[simp]
lemma one_mul_backrun.def {A : base} (a : A) : one_mul_backrun a = ⟨(), a⟩ := rfl

def distrib_backrun {A B C : base} : A * B + A * C → A * (B + C)
  | (inl ⟨a, b⟩) := ⟨a, inl b⟩ 
  | (inr ⟨a, c⟩) := ⟨a, inr c⟩

@[simp]
def distrib_backrun.inl {A B C : base} {a : A} {b : B} : 
  @distrib_backrun A B C (inl ⟨a, b⟩) = ⟨a, inl b⟩ := rfl

@[simp]
def distrib_backrun.inr {A B C : base} {a : A} {c : C} : 
  @distrib_backrun A B C (inr ⟨a, c⟩) = ⟨a, inr c⟩ := rfl

def distrib0_backrun (A : base) : (0 : base) → A * 0 
  | z := ⟨z.cases_on (λ _, A), z⟩

@[simp]
def distrib0_backrun.def (A : base) (z : (0 : base)) : 
  distrib0_backrun A z = (⟨z.cases_on (λ _, A), z⟩ : A * 0) := rfl

def subatomic.backrun : ∀ (s : subatomic) {A B : base}, s.typed A B → (B → A)
| subatomic.id := λ A B p, by {cases p, exact id}
| swap_add := λ A B p, by {cases p, exact sum.swap}
| subatomic.zero_add := λ A B p, by {cases p, exact inr}
| assoc_add := λ A B p, by {cases p, exact assoc_add_backrun}
| swap_mul := λ A B p, by {cases p, exact prod.swap}
| subatomic.one_mul := λ A B p, by {cases p, exact one_mul_backrun}
| assoc_mul := λ A B p, by {cases p, exact assoc_mul_backrun}
| subatomic.distrib := λ A B p, by {cases p, exact distrib_backrun}
| distrib0 := λ A B p, by {cases p, exact distrib0_backrun _}

universe u

def base.card : base → ℕ
  | zero := 0
  | one := 1
  | (base.add l r) := l.card + r.card
  | (base.mul l r) := l.card * r.card

def base.to_fin : ∀ {A : base} (v : A), fin (A.card) 
  | zero e := e.cases_on _ 
  | one _ := ⟨0, by {unfold base.card, exact nat.one_pos}⟩
  | (base.add l r) (inl v) :=
    let ⟨n, p⟩ := (base.to_fin v) in
    ⟨n, nat.lt_add_right n _ _ p⟩
  | (base.add l r) (inr v) :=
    let ⟨n, p⟩ := (base.to_fin v) in
    ⟨l.card + n, add_lt_add_left p (base.card l)⟩ 
  | (base.mul l r) ⟨vₗ, vᵣ⟩ :=
    let ⟨nₗ, pₗ⟩ := base.to_fin vₗ in
    let ⟨nᵣ, pᵣ⟩ := base.to_fin vᵣ in
    ⟨nₗ * r.card + nᵣ, by {
      unfold base.card,
      calc 
        nₗ * r.card + nᵣ < nₗ * r.card + r.card : add_lt_add_left pᵣ (nₗ * base.card r)
        ... = (nₗ + 1) * r.card : by {rw add_mul, rw _root_.one_mul}
        ... ≤ l.card * r.card : mul_le_mul_right' (nat.succ_le_iff.mpr pₗ) (base.card r)
    }⟩

@[simp]
lemma sum.swap_inl {α β} {a : α} : (sum.inl a : α ⊕ β).swap = inr a := rfl
@[simp]
lemma sum.swap_inr {α β} {b : β} : (sum.inr b : α ⊕ β).swap = inl b := rfl

@[simp]
lemma prod.swap_def {α β} (a : α) (b : β) : (⟨a,b⟩ : α × β).swap = ⟨b,a⟩ := rfl 

instance base.one.subsingleton : subsingleton (1 : base) := punit.subsingleton

def subatomic.run' : ∀ (s : subatomic) {A B}, s.typed A B → (A ≃ B) :=
  λ s A B p, ⟨s.run p, s.backrun p, by {
    intros a,
    cases p; unfold subatomic.run subatomic.backrun,
    {simp_rw id.def},
    {cases a; simp},
    {cases a, cases a, simp},
    {cases a, cases a, all_goals {simp}},
    {cases a; simp},
    {cases a; simp at *},
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

def atomic.run {A B : base} : ∀ (a : atomic), a.typed A B → A → B  
| (atomic.forward s) p :=  by {cases p, apply s.run, assumption}
| (atomic.backward s) p := by {cases p, apply s.backrun, assumption}

inductive pie.down.result (A B : base)
  | done : B → pie.down.result
  | left_context (f p : pie) (A' B' : base) : 
    p.typed A' B' → 
    (plug_in (add_left f) p).typed A B → 
    A' → 
    pie.down.result
  | right_context (p g : pie) (A' B' : base) : 
    p.typed A' B' → 
    (plug_in (add_right g) p).typed A B → 
    A' →
    pie.down.result
  | mul_contexts (f g : pie) (A' B' C' D' : base) :
    f.typed A' B' →
    g.typed C' D' →
    (plug_in (mul_left f) g).typed A B →
    (plug_in (mul_right g) f).typed A B →
    A' →
    C' → 
    pie.down.result
  | entering_comp (p : pie) (list : list pie) (right : pie) (A' B' : base) :
    p.typed A A' → 
    list.typed A' B' → 
    right.typed B' B →
    (plug_in (comp_left list right) p).typed A B →
    A → 
    pie.down.result

open pie.down.result

def pie.down : 
  ∀ (p : pie) {A B} (p_typed : p.typed A B), A → pie.down.result A B
  | (pie.atomic p_atom) A B (pie.typed.atomic .(p_atom) p_atom_typed) left_value :=
    done (p_atom.run p_atom_typed left_value)
  | (pie.add f g) 
    (.(A) + .(C)) (.(B) + .(D)) 
    (pie.typed.add A B C D .(f) .(g) f_typed g_typed) 
    left_value :=
      match left_value with
      | inl f_arg := 
        left_context g f A B f_typed (typed.add A B C D f g f_typed g_typed) f_arg
      | inr g_arg := 
        right_context g f C D g_typed (typed.add A B C D f g f_typed g_typed) g_arg
      end
  | (pie.mul f g)
    (.(A) * .(C)) (.(B) * .(D)) 
    (pie.typed.mul A B C D .(f) .(g) f_typed g_typed)
    left_value := 
      let h := typed.mul A B C D f g f_typed g_typed in
        mul_contexts g f C D A B g_typed f_typed h h left_value.snd left_value.fst
  | (pie.comp_list left list right)
    .(A) .(B)
    (pie.typed.comp_list A A' B' B left_typed list_typed right_typed)
    left_value := by {
      apply entering_comp left list right; try {assumption},
      apply pie.typed.comp_list; try {assumption},
    }

def am_state.step (now : am_state) : am_state ⊕ now.focus_right := 
  match now.value with
  | (inl left_value) := 
    match now.focus.run now.focus_typed left_value with
    | 
  | (inr right_value) := _
  

-- end abstract_machine

end
