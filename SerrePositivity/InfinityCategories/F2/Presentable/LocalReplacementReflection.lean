module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CommaInitialAdjunction
public import SerrePositivity.InfinityCategories.F2.Presentable.LocalReplacementComma
public import SerrePositivity.InfinityCategories.F1B.Localization.Reflective

/-!
概要：各対象の局所置換から、局所対象の全部分 ∞ 圏への反射を構成する。
方針：元の局所置換を comma 始対象へ移し、coherent な単位とその随伴普遍性を構成する。
規約：局所置換の存在は入力。presentable 性からの置換の存在は別工程。
使われ方：HTT 5.5.4.15 の局所置換から反射への部分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の各局所置換の辺の存在から、局所対象の全部分圏の反射性が従う。 -/
lemma isReflectiveSubcategory_of_localReplacements {X : SSet.{u}} [Quasicategory X]
    (W : Set (X _⦋1⦌))
    (hreplace : ∀ x : X _⦋0⦌, ∃ (y : X _⦋0⦌)
      (e : Truncated.Edge (X := (truncation 2).obj X) x y),
      e.edge ∈ localEquivalences W ∧ IsLocalObject W y) :
    IsReflectiveSubcategory X (IsLocalObject W) := by
  obtain ⟨F, ⟨a⟩⟩ := exists_qcatAdjunction_of_commaFiberInitial
    (localObjectsSubcomplex W).ι (unitCommaFiber_initial_exists_of_localReplacements W hreplace)
  exact ⟨⟨F, a⟩⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
