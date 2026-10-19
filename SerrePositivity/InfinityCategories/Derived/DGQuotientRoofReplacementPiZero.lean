module
public import SerrePositivity.InfinityCategories.Derived.DGCommonRoofComparisonVertices
public import SerrePositivity.InfinityCategories.Derived.RoofReplacementPiZero

/-! # 元の実屋根の全空間比較の連結成分上の全射性

概要：元の屋根から商側屋根への simplicial replacement 比較は π₀ 上全射。
方針：指定共通添字の有限係数頂点を細分後で持ち上げ、実輸送辺と実ホモトピーを使う。
規約：π₀ の全射性だけで弱同値性を主張しない。使われ方：β3 の全空間比較の基底。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite DifferentialGraded DGQuotient DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 元の屋根の比較の全空間は、商側の全空間の各連結成分を持ち上げる。 -/
theorem dgRoofReplacementComparison_piZero_surjective (P : Set D)
    (hP : localKFlat A D P) (x y : D) :
    Function.Surjective (SSet.mapπ₀ (dgRoofReplacementComparison A D P x y)) := by
  apply roofReplacementMap_piZero_surjective
  intro c g
  obtain ⟨d, r, t, hh⟩ := dgCommonRoofComparison_vertex_lifts A D P hP x
    (fun _ : Fin 1 => y) c (fun _ => g)
  refine ⟨d, r, t 0, ?_⟩
  let H := Classical.choice (hh 0)
  have h := SSet.π₀.sound (simplicialHomotopyVertexEdge H.homotopy
    (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{max u v}))))
  change SSet.π₀.mk (SSet.yonedaEquiv (SSet.yonedaEquiv.symm g ≫
      (dgCommonRoofQuotient A D P x y).map r)) =
    SSet.π₀.mk (SSet.yonedaEquiv (SSet.yonedaEquiv.symm (t 0) ≫
      (dgCommonRoofComparison A D P x y).app d)) at h
  simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h

end SerrePositivity.InfinityCategories
