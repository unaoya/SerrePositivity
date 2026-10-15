module

public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous
public import Mathlib.Order.SuccPred.Limit

/-! # Ordered prefixes below a limit stage

The inherited successor stays strictly below the limit. These explicit
structures do not require the prefix to have large cofinality.
-/

@[expose] public section
universe w
noncomputable section

namespace SerrePositivity.DiagramModel.LimitPrefix
variable {K : Type w} [LinearOrder K] [SuccOrder K] (j : K) (hj : Order.IsSuccLimit j)

@[instance_reducible]
def succOrder : SuccOrder (Set.Iio j) :=
  SuccOrder.ofSuccLeIff (fun i => ⟨Order.succ i.val, hj.succ_lt i.property⟩) (by
    intro a b
    change Order.succ a.val ≤ b.val ↔ a.val < b.val
    exact Order.succ_le_iff_of_not_isMax (not_isMax_iff.mpr ⟨j, a.property⟩))

lemma coe_succ (i : Set.Iio j) :
    let := succOrder j hj; (Order.succ i).val = Order.succ i.val := rfl

variable [OrderBot K]

@[instance_reducible]
def orderBot : OrderBot (Set.Iio j) := Subtype.orderBot (Ne.bot_lt' (by
  intro h
  subst j
  exact Order.not_isSuccLimit_bot hj))

omit [SuccOrder K] in
lemma coe_bot : let := orderBot j hj; ((⊥ : Set.Iio j) : K) = ⊥ := rfl

end SerrePositivity.DiagramModel.LimitPrefix
