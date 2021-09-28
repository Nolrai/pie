import data.list.pairwise
import data.list
import data.list.sort
import data.vector
import data.finset
import data.array.lemmas
import data.equiv.list
import data.equiv.fin
import data.equiv.fintype
import order.lexicographic
import data.hash_map
import data.nat.log
import data.subtype

def arg_list (i n : ℕ) := {v : vector (fin i) n // v.to_list.nodup}

def arg_list.to_vector {i n} (a : arg_list i n) := a.val
def arg_list.to_list {i n} (a : arg_list i n) := a.to_vector.to_list
def arg_list.to_nodup {i n} (a : arg_list i n) : a.to_list.nodup := a.prop

inductive rcmd (i : ℕ) : Type
| tog (arg : fin i) : rcmd
-- | swap : fin 4 → fin 4 → cmd
| cnot (args : arg_list i 2) : rcmd
| toffoli : arg_list i 3 → rcmd

open rcmd
def rcmd.rank {i} : rcmd i → ℕ
  | (tog _) := 1
  | (cnot _) := 2
  | (toffoli _) := 3

def rcmd4.repr : rcmd 4 → string
  | (tog a) :=
    "n" ++ repr a.val
  | (cnot a) :=
    "c" ++ repr a.to_vector.head ++ repr a.to_vector.tail.head
  | (toffoli a) :=
    "t" ++ repr a.to_vector.head ++ repr a.to_vector.tail.head ++ repr a.to_vector.tail.tail.head

instance : has_repr (rcmd 4) := {
  repr := rcmd4.repr
}


@[simp] lemma rcmd.rank_tog (size : ℕ) (i : fin size) : rcmd.rank (tog i) = 1 := rfl
@[simp] lemma rcmd.rank_cnot (size : ℕ) (i) : rcmd.rank (cnot i : rcmd size) = 2 := rfl
@[simp] lemma rcmd.rank_toffoli (size : ℕ) (i) : rcmd.rank (toffoli i : rcmd size) = 3 := rfl

def rcmd.args {i} : rcmd i → list (fin i)
  | (tog a) := [a]
  | (cnot a) := a.to_list
  | (toffoli a) := a.to_list

open function

def rcmd.to_nat_list {i} (x : rcmd i) : list ℕ := x.rank :: x.args.map (λ x, x.1)
def rcmd.le {i} (x y : rcmd i) := x.to_nat_list ≤ y.to_nat_list
lemma rcmd.le_refl {i} (x : rcmd i) : x.le x := le_refl x.to_nat_list
lemma rcmd.le_trans {i} (x y z : rcmd i) : x.le y → y.le z → x.le z :=
  @le_trans _ _ x.to_nat_list y.to_nat_list z.to_nat_list
lemma rcmd.to_pair_injective {i} (x y : rcmd i) : x.to_nat_list = y.to_nat_list → x = y := by {
  cases x; cases y; cases x; cases y; unfold rcmd.to_nat_list rcmd.args arg_list.to_list; simp; intros h;
    apply vector.eq; exact list.map_injective_iff.mpr fin.coe_injective h,
}
lemma rcmd.le_antisymm {i} (x y : rcmd i) : x.le y → y.le x → x = y := by {
  intros xy yx,
  apply rcmd.to_pair_injective x y,
  unfold rcmd.le at xy yx,
  apply le_antisymm; assumption,
}

def rcmd.le_decidable {i} : decidable_rel (rcmd.le : rcmd i → rcmd i → Prop) := fun x y,
  if h : x.to_nat_list ≤ y.to_nat_list
    then is_true h
    else is_false h

lemma rcmd.le_total {i} (x y : rcmd i) : x.le y ∨ y.le x := le_total x.to_nat_list y.to_nat_list

instance {i} : linear_order (rcmd i) := {
  le := rcmd.le,
  le_refl := rcmd.le_refl,
  le_trans := rcmd.le_trans,
  le_antisymm := rcmd.le_antisymm,
  decidable_le := rcmd.le_decidable,
  le_total := rcmd.le_total,
}

lemma nodup_tail {α} {x : α} {xs} : list.nodup (x :: xs) → list.nodup xs := list.nodup_of_nodup_cons
lemma nodup_3 {α} {x y z: α} [decidable_eq α] : [x,y,z].nodup ↔ (x ≠ y ∧ x ≠ z ∧ y ≠ z) := by {
  simp,
  rw ← and_assoc,
  have : (¬(x = y ∨ x = z) ∧ ¬y = z) = ((¬x = y ∧ ¬x = z) ∧ ¬y = z),
  {
    congr,
    apply propext,
    split; intros hyp_iff,
    split; intros hyp_not; apply hyp_iff,
    {left, exact hyp_not},
    {right, exact hyp_not},
    intros hyp_not,
    cases hyp_not,
    exact hyp_iff.left hyp_not,
    exact hyp_iff.right hyp_not,
  },
  rw this,
}

def rcmd.run {size : ℕ} : rcmd size → array size bool → array size bool
  | (tog i) := λ arr, arr.write i (not (arr.read i))
  | (cnot {val := ⟨[control, target], _⟩, property := _}) := λ arr,
    if arr.read control then (tog target).run arr else arr
  | (toffoli {val := ⟨[control_a, control_b, target], _⟩, property := d} ) := λ arr,
    if (arr.read control_a)
      then
        let d' := by {apply list.nodup_of_nodup_cons d} in
        (cnot ⟨⟨[control_b, target], rfl⟩, d'⟩ ).run arr
      else arr
  using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf rcmd.rank⟩]}

lemma arr_write_read_neq
  (size : ℕ) (i : fin size) {α} (arr : array size α) {x : α} :
  (arr.write i x).read i = x := by {
    exact array.read_write arr i x
}

lemma rcmd.run_self (size : ℕ) : ∀ (c : rcmd size) (arr), c.run (c.run arr) = arr
  | (rcmd.tog c) := λ arr, by {
    unfold rcmd.run,
    simp,
    ext,
    have : decidable (c = i) := by apply_instance,
    cases this,
    {
      rw array.read_write_of_ne,
      rw array.read_write_of_ne,
      all_goals {apply this},
    },
    {
      rw this,
      rw array.read_write,
    }
  }
  | (cnot {val := ⟨[control, target], p⟩, property := p2}) := λ arr, by {
    have : (cnot {val := ⟨[control, target], p⟩, property := p2}).run =
      λ arr, if arr.read control then (rcmd.tog target).run arr else arr := by {
        unfold rcmd.run
      },
    rw this, clear this,
    have : decidable (arr.read control) := by apply_instance,
    cases this,
    {
      simp_rw if_neg this,
      rw if_neg,
      exact this,
    },
    {
      simp at p2,
      simp_rw if_pos this,
      rw if_pos,
      apply rcmd.run_self,
      unfold rcmd.run,
      rw array.read_write_of_ne,
      exact this,
      symmetry,
      exact p2,
    },
  }
  | (toffoli {val := ⟨[control, control_b, target], p⟩, property := d}) := λ arr, by {
    have : (toffoli {val := ⟨[control, control_b, target], p⟩, property := d}).run =
      λ arr,
        if (arr.read control)
          then
            let d' := by {apply list.nodup_of_nodup_cons d} in
            (cnot ⟨⟨[control_b, target], rfl⟩, d'⟩ ).run arr
          else arr
      := by unfold rcmd.run,
    simp at this,
    rw this, clear this,
    have : decidable (arr.read control) := by apply_instance,
    cases this,
    {
      simp_rw if_neg this,
      rw if_neg,
      exact this,
    },
    {
      simp at d,
      simp_rw if_pos this,
      simp_rw rcmd.run_self,
      have : (((cnot {val := ⟨[control_b, target], _⟩, property := _}).run arr).read control),
      {
        have : ∀ p₁ p₂,
          (((cnot {val := ⟨[control_b, target], p₁⟩, property := p₂}).run arr).read control)
            = arr.read control,
        {
          intros,
          unfold rcmd.run,
          split_ifs,
          apply array.read_write_of_ne,
          intros hyp,
          apply d.left,
          right,
          symmetry,
          assumption,
          refl,
        },
        rw this,
        clear this,
        exact this,
      },
      rw if_pos this,
    },
  }
  using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf rcmd.rank⟩]}

instance : monad_fail list := {
  fail := λ _ _, []
}

def mk_arg_list {i : ℕ} {m} [monad m] [monad_fail m] (get : m (fin i)) : ∀ {n : ℕ}, m (arg_list i n)
  | 0 := pure ⟨vector.nil, list.nodup_nil⟩
  | (k + 1) :=
    do
    x <- get,
    ⟨xs, p⟩ <- (mk_arg_list : m (arg_list i k)),
    if h : x ∈ xs.to_list
      then monad_fail.fail "duplicate argument -> cull"
      else pure ⟨x ::ᵥ xs, by {
        rw vector.to_list_cons x xs,
        apply list.nodup_cons.mpr ⟨h, p⟩
      }⟩

def list_out (α) [fintype α] [linear_order α] : list α :=
  multiset.sort (≤) (fintype.elems α).val

lemma mem_list_out (α) [fintype α] [linear_order α] (x : α) : x ∈ list_out α := by {
  unfold list_out,
  rw multiset.mem_sort,
  rw ← finset.mem_def,
  exact fintype.complete x
}

lemma mem_bind_op {α β} {b : β} {l : list α} {f : α → list β} :
  b ∈ (l >>= f) ↔ ∃ a ∈ l, b ∈ f a := by {
  unfold has_bind.bind,
  apply list.mem_bind
}

def mem_mk_arg_list {i n} {a : arg_list i n} :
  a ∈ (mk_arg_list (list_out (fin i)) : list (arg_list i n)) := by {
    obtain ⟨⟨l, l_length⟩, l_nodup⟩ := a,
    revert l l_length l_nodup,
    induction n; intros,
    {
      rw list.length_eq_zero at l_length,
      cases l,
      unfold mk_arg_list,
      rw list.mem_pure,
      refl,
      {cases l_length}
    },
    {
      unfold mk_arg_list,
      simp_rw mem_bind_op,
      cases l,
      {cases l_length},
      use l_hd,
      split,
      {apply mem_list_out},
      use l_tl,
      {
        rw list.length_cons at *,
        exact nat.succ.inj l_length
      },
      {exact list.nodup_of_nodup_cons l_nodup},
      {
        split,
        apply n_ih,
        unfold mk_arg_list._match_1,
        rw dif_neg,
        rw list.mem_pure,
        congr,
        simp at *,
        exact l_nodup.left,
      }
    },
  }

def list.sort {α} [linear_order α] : list α → list α := list.merge_sort (≤)
def multiset.sort' {α} [linear_order α] : multiset α → list α := multiset.sort (≤)

def rcmd.elems' {i} : ℕ → list (rcmd i)
  | 1 := (list_out (fin i)).map tog
  | 2 := cnot <$> (mk_arg_list (list_out (fin i)))
  | 3 := toffoli <$> (mk_arg_list (list_out (fin i)))
  | n := monad_fail.fail "ignore"

def rcmd.elems {i} : list (rcmd i) :=
  rcmd.elems' 1 ++ rcmd.elems' 2 ++ rcmd.elems' 3 ++ rcmd.elems' 4

lemma rcmd.mem_elems {i} (c : rcmd i) : c ∈ (rcmd.elems : list (rcmd i)) := by {
  cases c; unfold rcmd.elems,
  {
    repeat {apply list.mem_append_left},
    unfold rcmd.elems',
    rw list.mem_map,
    use c,
    split,
    apply mem_list_out,
    refl,
  },
  {
    apply list.mem_append_left,
    apply list.mem_append_left,
    apply list.mem_append_right,
    unfold rcmd.elems',
    rw list.map_eq_map,
    rw list.mem_map,
    use c,
    split,
    apply mem_mk_arg_list,
    refl
  },
  {
    apply list.mem_append_left,
    apply list.mem_append_right,
    unfold rcmd.elems',
    rw list.map_eq_map,
    rw list.mem_map,
    use c,
    split,
    apply mem_mk_arg_list,
    refl
  },
}

instance (i : ℕ) : fintype (rcmd i) := {
  elems := rcmd.elems.to_finset,
  complete := λ c, by { rw list.mem_to_finset, exact rcmd.mem_elems c},
}

-- this is just a type restricted version of function.comp
infix `∘∘`:90 := λ {i}, ((∘) : (array i bool → array i bool) → (array i bool → array i bool) → (array i bool → array i bool))

def list.run {i} := list.foldl (λ a (b : rcmd i), a ∘∘ b.run) id

def encode_bit_list : list bool → (ℕ → ℕ) :=
  flip (list.foldl (λ n (b : bool), if b then bit1 n else bit0 n))

def list_array : ∀ {i}, list (array i bool)
  | 0 := [array.nil]
  | (n+1) := do
    arr ← (list_array : list (array n bool)),
    value ← [tt, ff],
    pure $ array.push_back arr value

def encode_array_fun {i} : (array i bool → array i bool) → (ℕ → ℕ) :=
  λ f, encode_bit_list $
    do
    arr <- list_array,
    (f arr).read <$> list_out (fin i)

def pr_hash_map (i : ℕ) (n : fin 12) : Type := hash_map ℕ (λ _, vector (rcmd i) n)
def pr_hash_map.insert {i n} : pr_hash_map i n → vector (rcmd i) n → pr_hash_map i n
  | h v := hash_map.insert h (encode_array_fun v.to_list.run 0) v

def programs2 : pr_hash_map 4 2 :=
  list.foldl pr_hash_map.insert (mk_hash_map (2 ^ 16)) $ do
    (c0 : rcmd 4) <- rcmd.elems,
    (c1 : rcmd 4) <- rcmd.elems,
    pure ⟨[c0, c1], rfl⟩

def can_go_infront1' (c : rcmd 4) : list (rcmd 4) := (λ v : vector _ 2, v.head) <$>
  list.filter (λ v : vector _ 2, v.tail.head = c) ((λ s : Σ _ : ℕ, vector (rcmd 4) 2, s.2) <$> programs2.entries)

def can_go_infront : hash_map (rcmd 4) (λ _, list (rcmd 4)) :=
  hash_map.insert_all ((λ c, ⟨c, can_go_infront1' c⟩) <$> rcmd.elems) (mk_hash_map 64)

def programs3 : pr_hash_map 4 3 :=
  let p := programs2.entries in
  list.foldl pr_hash_map.insert (mk_hash_map (2 ^ 16)) $ do
    ⟨_, (p1 : vector (rcmd 4) 2)⟩ <- p,
    ⟨_, (p2 : vector (rcmd 4) 2)⟩ <- p,
    if p2.head = p1.tail.head
      then pure (p1.head ::ᵥ p2)
      else []

-- times out at ~20 seconds
-- #eval programs3.entries.length

def array.unsplit {n m : ℕ} {α} (l : array n α) (r : array m α) : array (n + m) α :=
  {
    data :=
      λ i, if h : n ≤ i.val
        then r.read ⟨i.val - n, ((sub_lt_iff_left h).mpr i.prop)⟩
        else l.read ⟨i.val, not_le.mp h⟩
  }



def array.split_at (n : ℕ) (m : ℕ) {α} : array (n + m) α → array n α × array m α
  | {data := f} :=
    {
      fst := {data := λ i, f (fin.cast_add m i) },
      snd := {data := λ i, f ⟨n + i.val, add_lt_add_left i.prop n⟩}
    }

def run_ancilla (n : ℕ) {m : ℕ} (program : list (rcmd (m + n))) : array m bool → (array m bool × array n bool)
  | small_arr :=
    let big_arr : array (m + n) bool := small_arr.unsplit {data := λ _, ff} in
    (program.run big_arr).split_at m n

namespace list

variable {α : Type}

lemma lookup_eq_some_mem [decidable_eq α] {a x : α} {l : list _}  : list.lookup a l = some x → (a, x).to_sigma ∈ l := by {
  intros h,
  induction l,
  { rw list.lookup_nil at h, cases h},
  obtain ⟨a', x'⟩ := l_hd,
  have : decidable (a = a') := by apply_instance,
  cases this,
  {
    rw list.lookup_cons_ne at h,
    exact list.mem_cons_of_mem ⟨a', x'⟩ (l_ih h),
    simp,
    exact this,
  },
  {
    rw this at *,
    rw list.lookup_cons_eq at h,
    have x'_eq : x' = x := by {injection h},
    rw x'_eq at *, clear x'_eq h,
    apply list.mem_cons_self,
  }
}

lemma nodup_of_perm_of_nodup (l l₂ : list α) : l ~ l₂ → l.nodup → l₂.nodup :=
  by {intros, exact (list.perm.nodup_iff ᾰ).mp ᾰ_1}

lemma nmem_append_iff (a : α) (l₁ l₂ : list α) : (a ∉ l₁ ∧ a ∉ l₂) ↔ a ∉ (l₁ ++ l₂) := by {
  induction l₁,
  rw list.nil_append,
  simp,
  simp at *,
  split; intros h₁,
  cases h₁,
  intros h₂,
  cases h₂,
  apply h₁_left,
  left, assumption,
  cases h₂,
  apply h₁_left,
  right, assumption,
  apply h₁_right,
  exact h₂,
  split,
  intro h₂,
  apply h₁,
  cases h₂,
  left, assumption,
  right, left, assumption,
  intros h₂,
  apply h₁,
  right, right, assumption,
}

lemma nodup_of_insert
  (b : α) (l₂ l₁ : list α) (l₁l₂_nodup : (l₁ ++ b :: l₂).nodup) :
  (l₁ ++ l₂).nodup := by {
  induction l₁,
  {simp_rw list.nil_append at *, apply list.nodup_of_nodup_cons l₁l₂_nodup},
  simp_rw list.cons_append at *,
  simp_rw list.nodup_cons at *,
  split,
  rw [← list.nmem_append_iff] at *,
  split,
  exact l₁l₂_nodup.left.left,
  apply list.not_mem_of_not_mem_cons,
  exact l₁l₂_nodup.left.right,
  apply l₁_ih,
  exact l₁l₂_nodup.right,
}

lemma ne_of_nodup_append (a b : α) (l₁ l₂ : list α) :
  a ∈ l₁ → b ∈ l₂ → (l₁ ++ l₂).nodup → a ≠ b := by {
  intros a_in_l₁ b_in_l₂ l₁l₂_nodup,
  induction l₂; cases b_in_l₂,
  {
    rw ← b_in_l₂ at *,
    clear' l₂_hd b_in_l₂ l₂_ih,
    induction l₁; cases a_in_l₁,
    {
      rw ← a_in_l₁ at *,
      clear' l₁_hd a_in_l₁ l₁_ih,
      simp at *,
      obtain ⟨nodup_left, nodup_right⟩ := l₁l₂_nodup,
      intros h,
      apply nodup_left,
      right, left, assumption,
    },
    apply l₁_ih,
    {assumption},
    apply list.nodup_of_nodup_cons l₁l₂_nodup,
  },
  apply l₂_ih; clear l₂_ih,
  {assumption},
  clear_except l₁ l₂ l₁l₂_nodup,
  clear a_in_l₁,
  apply nodup_of_insert,
  assumption,
}

lemma split_at_mem
  {a : α} {l : list α} (a_in_l : a ∈ l) :
  ∃ (llₗ llᵣ : list α), l = llₗ ++ a :: llᵣ := by {
  induction l; cases a_in_l,
  cases a_in_l, clear a_in_l,
  use [nil, l_tl],
  simp,
  have := l_ih a_in_l,
  obtain ⟨llₗ, llᵣ, eq_l⟩ := this,
  use [l_hd :: llₗ, llᵣ],
  rw eq_l,
  simp,
}

lemma mem_split_at_mem
  {a b : α} {l : list α}
  (a_in_l : a ∈ l)
  (b_in_l : b ∈ l)
  (a_ne_b : a ≠ b) :
  ∃ (llₗ llᵣ : list α),
    l = llₗ ++ a :: llᵣ ∧
      (b ∈ llₗ ∨ b ∈ llᵣ) := by {
  have := split_at_mem a_in_l, clear a_in_l,
  obtain ⟨llₗ, llᵣ, eq_l⟩ := this,
  use [llₗ, llᵣ],
  split, {assumption},
  rw eq_l at *, clear eq_l,
  have : b ∈ llₗ ∨ b ∈ a :: llᵣ := by {exact mem_append.mp b_in_l},
  cases this, {left, assumption},
  cases this, {exfalso, apply a_ne_b, symmetry, assumption},
  right, assumption,
}

lemma map_snd_of_zip (lₗ lᵣ : list α) (length_ok : lᵣ.length ≤ lₗ.length) :
  prod.snd <$> lₗ.zip lᵣ = lᵣ := by {
  revert lₗ,
  induction lᵣ, {simp},
  intros,
  cases lₗ, {simp at length_ok, cases length_ok},
  simp at *,
  apply lᵣ_ih _ length_ok,
}

end list

section perm_of_elems_equiv_bijection

parameters {α : Type} [linear_order α] [fintype α]

section to_fun

parameter (l : {l : list α // (fintype.elems α).sort (≤) ~ l})

def lookup_list : list (Σ x : α, α) := prod.to_sigma <$> ((fintype.elems α).sort (≤)).zip l.val
def lookup_list_inv : list (Σ x : α, α) := prod.to_sigma <$> l.val.zip ((fintype.elems α).sort (≤))


def option.from_some {α} : ∀ (x : option α), x ≠ none → α
  | (some a) _ := a
  | none p := by {exfalso, apply p, refl}

lemma option.from_some_injective {α} : ∀ {x y : option α} {px py},
  x.from_some px = y.from_some py → x = y
  | (some a) (some .(a)) _ _ rfl := rfl
  | none _ px _ h := by {exfalso, apply px, refl}
  | _ none _ py h := by {exfalso, apply py, refl}

lemma option.from_some_eq_iff {α : Type} : ∀ {x : option α} {p : x ≠ none} {a : α},
  x.from_some p = a ↔ x = some a := by {
    intros,
    cases x,
    exfalso,
    apply p,
    refl,
    rw option.from_some,
    split; intro h,
    congr; apply h,
    injection h,
  }

lemma option.some_from_some {α} {x : option α} {p} : some (x.from_some p) = x := by {
  cases x,
  {exfalso, apply p, refl},
  rw option.from_some,
}

def to_fun_val (a : α) : α :=
  (list.lookup a lookup_list).from_some
    (by {
      intros eq_none,
      rw list.lookup_eq_none at eq_none,
      apply eq_none,
      rw lookup_list,
      rw list.keys,
      unfold functor.map,
      rw list.map_map,
      have :
        list.map (sigma.fst ∘ prod.to_sigma) ((finset.sort has_le.le (fintype.elems α)).zip l.val) =
          finset.sort has_le.le (fintype.elems α),
      {
        unfold comp,
        simp,
        rw list.map_fst_zip,
        apply le_of_eq,
        apply list.perm.length_eq,
        apply l.prop,
      },
      rw this, clear this,
      rw finset.mem_sort,
      apply fintype.complete,
    })

def to_fun_val_inv (a : α) : α :=
  (list.lookup a lookup_list_inv).from_some
    (by {
      intros eq_none,
      rw list.lookup_eq_none at eq_none,
      apply eq_none,
      rw lookup_list_inv,
      rw list.keys,
      unfold functor.map,
      rw list.map_map,
      have :
        list.map (sigma.fst ∘ prod.to_sigma) (l.val.zip (finset.sort has_le.le (fintype.elems α))) =
          l,
      {
        unfold comp,
        simp,
        rw list.map_fst_zip,
        apply le_of_eq,
        apply list.perm.length_eq,
        apply l.prop.symm,
      },
      rw this, clear this,
      rw ← list.perm.mem_iff l.prop,
      rw finset.mem_sort,
      apply fintype.complete,
    })

lemma to_fun_aux {a : α} : (a, to_fun_val a).to_sigma ∈ lookup_list := by {
  apply list.lookup_eq_some_mem,
  rw to_fun_val,
  rw option.some_from_some,
}

lemma to_fun_injective : injective to_fun_val := by {
  intros a₁ a₂ f_a₁_eq_f_a₂,
  have a₁_f_a₁_in_lookup_list : (a₁, to_fun_val a₁).to_sigma ∈ lookup_list,
  apply to_fun_aux,
  have a₁_f_a₂_in_lookup_list : (a₂, to_fun_val a₁).to_sigma ∈ lookup_list,
  rw f_a₁_eq_f_a₂,
  apply to_fun_aux,
  have a₁_a₂ : decidable (a₁ = a₂) := by apply_instance,
  cases a₁_a₂, rotate, exact a₁_a₂, rotate,

  suffices : ∃ l₁ l₂ a, a ∈ l₁ ∧ a ∈ l₂ ∧ l₁ ++ l₂ = l.val,
  {
    exfalso,
    have l_nodup : l.val.nodup,
    {
      apply (list.perm.nodup_iff l.prop).mp,
      exact finset.sort_nodup has_le.le (fintype.elems α)
    },
    obtain ⟨l₁, l₂, a, a_in_l₁, a_in_l₂, l₁l₂_eq_l⟩ := this,
    suffices : a ≠ a, {apply this, refl},
    apply list.ne_of_nodup_append,
    apply a_in_l₁,
    apply a_in_l₂,
    rw l₁l₂_eq_l,
    assumption,
  },

  have : ∃ llₗ llᵣ,
    lookup_list = llₗ ++ (a₁, to_fun_val a₁).to_sigma :: llᵣ ∧
      ((a₂, to_fun_val a₁).to_sigma ∈ llₗ ∨ (a₂, to_fun_val a₁).to_sigma ∈ llᵣ),
  {
    apply list.mem_split_at_mem; try {assumption},
    intros ne_hyp,
    apply a₁_a₂,
    cases ne_hyp,
    refl,
  }, clear f_a₁_eq_f_a₂ a₁_f_a₁_in_lookup_list a₁_f_a₂_in_lookup_list,
  obtain ⟨llₗ, llᵣ, lookup_list_eq, in_ll⟩ := this,

  {
    rcases in_ll with (in_llₗ | in_llᵣ),
    {
      set to_snd : (Σ (x : α), α) → α := sigma.snd with to_snd_def,
      have lookup_eq_2 : to_snd <$> lookup_list = to_snd <$> llₗ ++ to_fun_val a₁ :: to_snd <$> llᵣ,
      rw lookup_list_eq,
      simp,
      use [to_snd <$> llₗ, to_fun_val a₁ :: to_snd <$> llᵣ, to_fun_val a₁],
      split,
      {
        unfold functor.map,
        rw list.mem_map,
        use (a₂, to_fun_val a₁).to_sigma,
        split,
        exact in_llₗ,
        unfold prod.to_sigma,
      },
      split, {apply list.mem_cons_self},
      {
        transitivity (to_snd <$> lookup_list),
        symmetry,
        exact lookup_eq_2,
        rw lookup_list,
        have : ∀ l : list (α × α), to_snd <$> prod.to_sigma <$> l = prod.snd <$> l,
        {
          clear_except,
          intros,
          unfold functor.map,
          induction l,
          simp_rw list.map_nil,
          simp_rw list.map_cons,
          obtain ⟨x, y⟩ := l_hd,
          simp,
          rw ← l_ih,
          symmetry,
          apply list.map_map,
        },
        rw this, clear this,
        rw list.map_snd_of_zip,
        apply le_of_eq,
        apply list.perm.length_eq,
        symmetry,
        exact l.prop,
      }
    },
    {
      set to_snd : (Σ (x : α), α) → α := sigma.snd with to_snd_def,
      have lookup_eq_2 :
        to_snd <$> lookup_list = to_snd <$> llₗ ++ [to_fun_val a₁] ++ to_snd <$> llᵣ,
      {
        rw lookup_list_eq,
        simp,
      },
      use [to_snd <$> llₗ ++ [to_fun_val a₁], to_snd <$> llᵣ, to_fun_val a₁],
      split,
      {
        apply list.mem_append_right,
        apply list.mem_cons_self,
      },
      split,
      {
        unfold functor.map,
        rw list.mem_map,
        use (a₂, to_fun_val a₁).to_sigma,
        split,
        exact in_llᵣ,
        unfold prod.to_sigma,
      },
      {
        transitivity (to_snd <$> lookup_list),
        symmetry,
        exact lookup_eq_2,
        rw lookup_list,
        have : ∀ l : list (α × α), to_snd <$> prod.to_sigma <$> l = prod.snd <$> l,
        {
          clear_except,
          intros,
          unfold functor.map,
          induction l,
          simp_rw list.map_nil,
          simp_rw list.map_cons,
          obtain ⟨x, y⟩ := l_hd,
          simp,
          rw ← l_ih,
          symmetry,
          apply list.map_map,
        },
        rw this, clear this,
        rw list.map_snd_of_zip,
        apply le_of_eq,
        apply list.perm.length_eq,
        symmetry,
        exact l.prop,
      }
    }
  }
}

def to_fun_surjective : surjective to_fun_val := by {
  unfold surjective,
  intros b,

}

def to_fun : {f : α → α // bijective f} :=
  ⟨to_fun_val,
    by {
      split,


-- now onto surjectivity

    }
  ⟩

end to_fun

lemma ordered_fintype.perm_of_elems_equiv_to_equiv :
  {l : list α // (fintype.elems α).sort (≤) ~ l} ≃ (α ≃ α) := {
    to_fun := to_fun,
    inv_fun := _,
    left_inv := _,
    right_inv := _,
  }

end perm_of_elems_equiv_bijection

lemma rcmd.taffoli_universal :
  ∀ n (f : array n bool ≃ array n bool),
    ∃ (program : list (rcmd (n + 2))), ∀ input,
      (run_ancilla 2 program input) = (f input, {data := λ _, ff}) := by {
  intros n f,



}