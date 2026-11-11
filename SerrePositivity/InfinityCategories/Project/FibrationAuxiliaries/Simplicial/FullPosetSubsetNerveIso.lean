module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.PosetLowerTerminalFunctor
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
概要：全ての点を含む順序部分型の包含が誘導する nerve 写像は同型である。
方針：包含関手の充満忠実性と対象全単射から圏の厳密な同型を回収する。
規約：元の順序包含の nerve 写像自身を使う。
使われ方：下方閉部分を固定する有限半順序帰納の全体基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
/-- 概要：全ての点を含む順序部分型の元の包含は圏の同型。
方針：対象全単射と順序の充満性。規約：包含関手。使われ方：全体基底。 -/
lemma fullPosetSubsetInclusion_isIso {P : Type u} [PartialOrder P]
    (U : Set P) (hU : ∀ p, p ∈ U) : (OrderHom.Subtype.val U).toFunctor.IsIso := by
  refine { faithful := ?_, full := ?_, bijective_obj := ?_ }
  · constructor
    intro x y f g h
    exact Subsingleton.elim _ _
  · constructor
    intro x y f
    exact ⟨homOfLE (leOfHom f), Subsingleton.elim _ _⟩
  · exact ⟨Subtype.val_injective, fun p ↦ ⟨⟨p, hU p⟩, rfl⟩⟩

/-- 概要：全ての点を含む部分型への元の形状制限は同型。
方針：包含関手の厳密な逆を nerve に写す。
規約：元の包含写像。使われ方：指定余錐持ち上げの基底。 -/
lemma fullPosetSubsetNerveMap_isIso {P : Type u} [PartialOrder P]
    (U : Set P) (hU : ∀ p, p ∈ U) :
    IsIso (nerveMap (OrderHom.Subtype.val U).toFunctor) := by
  letI := fullPosetSubsetInclusion_isIso U hU
  let e := (OrderHom.Subtype.val U).toFunctor.asIsomorphism
  refine ⟨⟨nerveMap e.inverse, ?_, ?_⟩⟩
  · change nerveMap (e.functor ⋙ e.inverse) = nerveMap (𝟭 _)
    rw [e.unit_eq]
  · change nerveMap (e.inverse ⋙ e.functor) = nerveMap (𝟭 _)
    rw [e.counit_eq]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
