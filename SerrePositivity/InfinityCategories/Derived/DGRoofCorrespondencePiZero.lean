module
public import SerrePositivity.InfinityCategories.Derived.DGStrictQuotientRoofPiZero
public import SerrePositivity.InfinityCategories.Derived.DGStrictMappedRoofVertexInverse

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 任意の実商屋根頂点は、元の実屋根の像と同じ連結成分にある。 -/
theorem dgQuotientRoofVertex_exists_image_piZero (P : Set D) (hP : localKFlat A D P)
    (x y : D) (z : (dgQuotientRoofCorrespondence A D P x y) _⦋0⦌) :
    ∃ v : (dgRoofCorrespondence A D P x y) _⦋0⦌,
      SSet.π₀.mk ((dgRoofCorrespondenceMap A D P x y).app (Opposite.op ⦋0⦌) v) =
        SSet.π₀.mk z := by
  let s := dgMappedRoofVertexDenominator A D (QuotientObject D P)
    (inclusion A D P) P x ((inclusion A D P).obj y) z
  let f := dgMappedRoofVertexNumerator A D (QuotientObject D P)
    (inclusion A D P) P x ((inclusion A D P).obj y) z
  obtain ⟨v, hv⟩ := dgStrictQuotientRoofVertex_exists_image_piZero A D P hP x y s f
  refine ⟨v, hv.trans ?_⟩
  exact congrArg SSet.π₀.mk (dgStrictMappedRoofVertex_rightInverse A D (QuotientObject D P)
    (inclusion A D P) P x ((inclusion A D P).obj y) z)

/-- 元の実屋根の商比較は、連結成分上で全射。 -/
theorem dgRoofCorrespondenceMap_piZero_surjective (P : Set D) (hP : localKFlat A D P)
    (x y : D) :
    Function.Surjective (SSet.mapπ₀ (dgRoofCorrespondenceMap A D P x y)) := by
  intro z
  obtain ⟨w, rfl⟩ := SSet.π₀.mk_surjective z
  obtain ⟨v, hv⟩ := dgQuotientRoofVertex_exists_image_piZero A D P hP x y w
  exact ⟨SSet.π₀.mk v, hv⟩

end SerrePositivity.InfinityCategories
