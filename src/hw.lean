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

def arg_list (i n : ℕ) := {v : vector (fin i) n // v.to_list.nodup}

def arg_list.to_vector {i n} (a : arg_list i n) := a.val
def arg_list.to_list {i n} (a : arg_list i n) := a.to_vector.to_list
def arg_list.to_nodup {i n} (a : arg_list i n) : a.to_list.nodup := a.prop

inductive rcmd (i : ℕ) : Type
| tog (arg : fin i) : rcmd
-- | swap : fin 4 → fin 4 → cmd
| cnot (args : arg_list i 2) : rcmd
| toffoli : arg_list i 3 → rcmd
| fredkin : arg_list i 3 → rcmd

open rcmd
def rcmd.rank {i} : rcmd i → ℕ
  | (tog _) := 1
  | (cnot _) := 2
  | (toffoli _) := 3
  | (fredkin _) := 4

def rcmd4.repr : rcmd 4 → string
  | (tog a) :=
    "n" ++ repr a.val
  | (cnot a) :=
    "c" ++ repr a.to_vector.head ++ repr a.to_vector.tail.head
  | (toffoli a) :=
    "t" ++ repr a.to_vector.head ++ repr a.to_vector.tail.head ++ repr a.to_vector.tail.tail.head
  | (fredkin a) :=
    "f" ++ repr a.to_vector.head ++ repr a.to_vector.tail.head ++ repr a.to_vector.tail.tail.head

instance : has_repr (rcmd 4) := {
  repr := rcmd4.repr
}


@[simp] lemma rcmd.rank_tog (size : ℕ) (i : fin size) : rcmd.rank (tog i) = 1 := rfl
@[simp] lemma rcmd.rank_cnot (size : ℕ) (i) : rcmd.rank (cnot i : rcmd size) = 2 := rfl
@[simp] lemma rcmd.rank_toffoli (size : ℕ) (i) : rcmd.rank (toffoli i : rcmd size) = 3 := rfl
@[simp] lemma rcmd.rank_fredkin (size : ℕ) (i) : rcmd.rank (fredkin i : rcmd size) = 4 := rfl

def rcmd.args {i} : rcmd i → list (fin i)
  | (tog a) := [a]
  | (cnot a) := a.to_list
  | (toffoli a) := a.to_list
  | (fredkin a) := a.to_list

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
  | (fredkin {val := ⟨[control, target_a, target_b], _⟩, property := _}) := λ arr,
    if arr.read control
      then (arr.write target_a (arr.read target_b)).write target_b (arr.read target_a)
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
  | (fredkin {val := ⟨[control, target_a, target_b], _⟩, property := d}) := λ arr, by {
    unfold vector.to_list at d,
    rw nodup_3 at d,
    obtain ⟨contro_ne_target_a, control_ne_target_b, target_a_ne_target_b⟩ := d,
    unfold rcmd.run,
    have : ((arr.write target_a (arr.read target_b)).write target_b (arr.read target_a)).read control =
      arr.read control,
    {
      rw array.read_write_of_ne,
      rw array.read_write_of_ne,
      symmetry,
      assumption,
      symmetry,
      assumption,
    },
    split_ifs; try {rw this}; clear this,
    {
      ext,
      have eq_a : decidable (i = target_a) := by apply_instance,
      cases eq_a with ne_a eq_a,
      {
        have eq_b : decidable (i = target_b) := by apply_instance,
        cases eq_b with ne_b eq_b,
        {
          repeat {rw array.read_write_of_ne},
          all_goals {symmetry, assumption},
        },
        {
          rw eq_b, clear ne_a eq_b i,
          rw array.read_write,
          rw array.read_write_of_ne _ _ target_a_ne_target_b.symm,
          rw array.read_write,
        }
      },
      {
          rw eq_a, clear eq_a i,
          rw array.read_write,
          rw array.read_write_of_ne _ _ target_a_ne_target_b.symm,
          rw array.read_write,
      }
    },
    {
      exfalso,
      apply h_1,
      rw array.read_write_of_ne,
      rw array.read_write_of_ne,
      exact h,
      all_goals {symmetry, assumption}
    },
    refl,
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

lemma list.mem_bind_op {α β} {b : β} {l : list α} {f : α → list β} :
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
      simp_rw list.mem_bind_op,
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
  | 4 := fredkin <$> (mk_arg_list (list_out (fin i)))
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
  {
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

set_option profiler true
set_option timeout 0

#eval (rcmd.elems : list (rcmd 4)).length

#eval programs2.entries.length
#eval programs3.entries.length

def programs5 : pr_hash_map 4 5 :=
  list.foldl pr_hash_map.insert (mk_hash_map (2 ^ 16)) $ do
    ⟨_, (p2 : vector (rcmd 4) 2)⟩ <- programs2.entries,
    ⟨_, (p3 : vector (rcmd 4) 3)⟩ <- programs3.entries,
    pure (p2.append p3)

def programs10 : pr_hash_map 4 10 :=
  list.foldl pr_hash_map.insert (mk_hash_map (2 ^ 16)) $ do
    ⟨_, (p2 : vector (rcmd 4) 5)⟩ <- programs5.entries,
    ⟨_, (p3 : vector (rcmd 4) 5)⟩ <- programs5.entries,
    pure (p2.append p3)

#eval programs10.entries.length

#check pr_hash_map 4 11

def programs11 : pr_hash_map 4 (11 : fin 12) :=
  list.foldl pr_hash_map.insert (mk_hash_map (2 ^ 16)) $ do
    (c : rcmd 4) <- rcmd.elems,
    ⟨_, (p : vector (rcmd 4) 10)⟩ <- programs10.entries,
    pure (c ::ᵥ p)