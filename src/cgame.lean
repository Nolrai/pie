import data.fin.basic
import set_theory.ordinal_notation
universe u

inductive pgame : Type (u + 1)
  | mk : ∀ {l_index r_index : Type u} (l : l_index → pgame) (r : r_index → pgame), pgame

def pgame.left_index : pgame → Type
  | (@pgame.mk l_index _ _ _) := l_index

def pgame.left_options : ∀ g : pgame, g.left_index → pgame
  | (@pgame.mk _ _ l _) := l

def pgame.right_index : pgame → Type
  | (@pgame.mk _ r_index _ _) := r_index

def pgame.right_options : ∀ g : pgame, g.right_index → pgame
  | (@pgame.mk _ _ _ r) := r

abbreviation list.fin_nth {α} (l : list α) (x : fin l.length) : α
  := l.nth_le x.val x.property

def of_lists (l r : list pgame) : pgame := ⟨l.fin_nth, r.fin_nth⟩

def pgame.neg : pgame → pgame
  | (pgame.mk l r) := pgame.mk (λ x, (r x).neg) (λ x, (l x).neg)

instance : has_neg pgame := {neg := pgame.neg}

lemma pgame.neg_def (α β) (l : α → pgame) (r : β → pgame) :
  - (pgame.mk l r) = pgame.mk (λ x, -(r x)) (λ x, -(l x)) := rfl

lemma pgame.neg_neg (g : pgame) : -(- g) = g := by {
  induction g with α β l r l_ih r_ih,
  simp_rw pgame.neg_def,
  repeat {split; try {refl}; try {apply heq_of_eq, funext}},
  {rw l_ih},
  {rw r_ih}
}

def pgame.sublabling : pgame → pgame → Prop
  | (pgame.mk al ar) (pgame.mk bl br) :=
    (∀ i, ∃ j, bl j = al i) ∧ (∀ i, ∃ j, br j = ar i)

def pgame.relabling (g h : pgame) :=
  g.sublabling h ∧ h.sublabling g

def pgame.relabling_exists_left (P : pgame → Prop) (g h : pgame) 
  (g_rel_h : g.relabling h) :
  (∃ i, P (g.left_options i)) ↔ (∃ i, P (h.left_options i)) := by {
    cases g, 
    cases h, 
    obtain ⟨g_subl_h, h_subl_g⟩ := g_rel_h, 
    cases g_subl_h, 
    cases h_subl_g, 
    split; intros hyp; obtain ⟨i, hyp⟩ := hyp,
    unfold pgame.left_options at *,
    rw pgame.left_index at *,e
  } 

def pgame.add (g h : pgame) : pgame := by {
  induction g with glix grix gL gR ih_gl ih_gr generalizing h,
  induction h with hlix hrix hL hR ih_hl ih_hr,
  let h : pgame := ⟨hL, hR⟩,
  refine @pgame.mk (glix ⊕ hlix) (grix ⊕ hrix) (sum.rec _ _) (sum.rec _ _),
  all_goals {intros ix},
  exact (ih_gl ix h),
  exact (ih_hl ix),
  exact (ih_gr ix h),
  exact (ih_hr ix),
}

instance : has_add pgame := {add := pgame.add}

def pgame.as_second : pgame → (Prop × Prop) := by {
  intros g,
  induction g with glix grix gl gr gl_ih gr_ih,
  split,
  {exact (¬ ∃ i : grix, (gr_ih i).2)},
  {exact (¬ ∃ i : glix, (gl_ih i).1)},
}

def pgame.as_second_def {l_index r_index l r} : (@pgame.mk l_index r_index l r).as_second =
  ⟨¬ ∃ i : r_index, (r i).as_second.2, ¬ ∃ i : l_index, (l i).as_second.1⟩ := rfl 

def pgame.as_second_relableing (g h : pgame) : g.relabling h → g.as_second = h.as_second := by {
  induction g generalizing h,
  cases h,
  intros g_rel_h,
  simp_rw pgame.as_second_def,
  congr' 2,
}

def pgame.ge_zero : pgame → Prop := λ g, (pgame.as_second g).1 
def pgame.le_zero : pgame → Prop := λ g, (pgame.as_second g).2
def pgame.is_pos := λ g : pgame, g.ge_zero ∧ ¬ g.le_zero
def pgame.is_neg := λ g : pgame, ¬ g.ge_zero ∧ g.le_zero
def pgame.is_zero := λ g : pgame, g.ge_zero ∧ g.le_zero
def pgame.fuzzy_with_zero := λ g : pgame, ¬ g.ge_zero ∧ ¬ g.le_zero

instance : has_sub pgame := ⟨λ g h, g + -h⟩
lemma pgame.sub_def (g h : pgame) : g - h = g + -h := rfl

def pgame.equiv (g h : pgame) : Prop := (g - h).is_zero
lemma pgame.equiv_def (g h : pgame) : g.equiv h = (g - h).is_zero := rfl

