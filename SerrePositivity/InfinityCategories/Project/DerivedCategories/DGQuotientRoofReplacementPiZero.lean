module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommonRoofComparisonVertices
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofReplacementPiZero

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded DGQuotient SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 元の屋根の比較の全空間は、商側の全空間の各連結成分を持ち上げる。 -/
theorem dgRoofReplacementComparison_piZero_surjective (P : Set D)
    (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P) (x y : D) :
    Function.Surjective (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofReplacementComparison A D P x y)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofReplacementMap_piZero_surjective
  intro c g
  obtain ⟨d, r, t, hh⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofComparison_vertex_lifts A D P hP x
    (fun _ : Fin 1 => y) c (fun _ => g)
  refine ⟨d, r, t 0, ?_⟩
  let H := Classical.choice (hh 0)
  have h := SSet.π₀.sound (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H.homotopy
    (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{max u v}))))
  change SSet.π₀.mk (SSet.yonedaEquiv (SSet.yonedaEquiv.symm g ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofQuotient A D P x y).map r)) =
    SSet.π₀.mk (SSet.yonedaEquiv (SSet.yonedaEquiv.symm (t 0) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommonRoofComparison A D P x y).app d)) at h
  simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
