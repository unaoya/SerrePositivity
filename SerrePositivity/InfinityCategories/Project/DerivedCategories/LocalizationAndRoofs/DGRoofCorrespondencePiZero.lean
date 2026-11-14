module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGStrictQuotientRoofPiZero
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGStrictMappedRoofVertexInverse

/-! # 実屋根比較の連結成分上の全射性

概要：元の実屋根から商側の実屋根への比較は、連結成分上で全射。
方針：任意の商側の実頂点を閉屋根で表示し、指定閉分子の細分後の持ち上げに戻す。
規約：高次ホモトピーの同型は未主張。使われ方：β3 の実屋根比較の零次元の基底。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 任意の実商屋根頂点は、元の実屋根の像と同じ連結成分にある。 -/
theorem dgQuotientRoofVertex_exists_image_piZero (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (x y : D) (z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondence A D P x y) _⦋0⦌) :
    ∃ v : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y) _⦋0⦌,
      SSet.π₀.mk ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y).app (Opposite.op ⦋0⦌) v) =
        SSet.π₀.mk z := by
  let s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappedRoofVertexDenominator A D (QuotientObject D P)
    (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) P x ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) z
  let f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappedRoofVertexNumerator A D (QuotientObject D P)
    (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) P x ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) z
  obtain ⟨v, hv⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictQuotientRoofVertex_exists_image_piZero A D P hP x y s f
  refine ⟨v, hv.trans ?_⟩
  exact congrArg SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictMappedRoofVertex_rightInverse A D (QuotientObject D P)
    (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P) P x ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) z)

/-- 元の実屋根の商比較は、連結成分上で全射。 -/
theorem dgRoofCorrespondenceMap_piZero_surjective (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (x y : D) :
    Function.Surjective (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)) := by
  intro z
  obtain ⟨w, rfl⟩ := SSet.π₀.mk_surjective z
  obtain ⟨v, hv⟩ := dgQuotientRoofVertex_exists_image_piZero A D P hP x y w
  exact ⟨SSet.π₀.mk v, hv⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
