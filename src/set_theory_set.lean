import order.lattice
import set_theory.ordinal_notation

universe u

inductive preset : Type (u + 1)
  | mk {α : Type u} (f : α → preset) : preset

open preset

def preset.ni : preset → preset → Prop
  | (mk f) x := ∃ i, x = f i

instance : has_mem preset preset := 
  {mem := λ small big, big.ni small}

def preset.subset : preset → preset → Prop :=
  λ x y, ∀ z, z ∈ x → z ∈ y

def preset.equiv0 : preset → preset → Prop :=
  λ x y, x.subset y ∧ y.subset x

def pruning_of : preset → preset → Prop
  | (mk f) (mk g) := 
    ∀ i, ∃ j, pruning_of (f i) (g j)

lemma pruning_of.refl {x} : pruning_of x x := by {
  induction x,
  rw pruning_of,
  intros ix,
  use ix,
  apply x_ih,
}

lemma pruning_of.trans {x y z} : pruning_of x y → pruning_of y z → pruning_of x z := by {
  induction x generalizing y z; cases y; cases z,
  simp_rw pruning_of,
  intros xy yz x_ix,
  obtain ⟨y_j, y_j_h⟩ := xy x_ix,
  obtain ⟨z_j, z_j_h⟩ := yz y_j,
  use z_j,
  apply x_ih,
  exact y_j_h,
  apply z_j_h,
}

instance : setoid preset := 
{
  r := λ x y, pruning_of x y ∧ pruning_of y x,
  iseqv := by {
    refine ⟨_, _, _⟩,
    { -- reflexivity
      intros x,
      apply (and_self _).mpr,
      exact pruning_of.refl,
    },
    { -- symmetry
      intros x y h,
      obtain ⟨h₁, h₂⟩ := h,
      exact ⟨h₂, h₁⟩
    },
    {
      intros x y z xy yz,
      obtain ⟨xy, yx⟩ := xy,
      obtain ⟨yz, zy⟩ := yz,
      split; apply pruning_of.trans; assumption,
    }
  }
}

def stset := quotient preset.setoid

def stset.mem : stset → stset → Prop := 
  let f (small big : preset) : Prop :=
  
  in quotient.lift₂ 