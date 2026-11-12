module

public import SerrePositivity.KST.Spectra.PathContractionEndpoint

/-!
概要：一つの path の頂点を、定数 path から始まる収縮の辺へ移す。
方針：path の収縮のパラメータを固定し、両端と終点を厳密に計算する。
規約：辺の頂点零が定数 path、頂点一が元の path。
使われ方：Goerss–Jardine I §7–8。円の成分と零 loop 同値の向き。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 指定した path の定数 path からの収縮の辺。 -/
def pathVertexContraction (Y : PointedSimplicialSet.{u})
    (v : (basedPathSpace Y).right _⦋0⦌) : (Δ[1] : SSet.{u}) ⟶ (basedPathSpace Y).right :=
  lift (SSet.const v) (𝟙 (Δ[1] : SSet.{u})) ≫ pathContraction Y

/-- 収縮の辺の頂点一は指定した path。 -/
lemma pathVertexContraction_face_zero (Y : PointedSimplicialSet.{u})
    (v : (basedPathSpace Y).right _⦋0⦌) :
    stdSimplex.δ (0 : Fin 2) ≫ pathVertexContraction Y v = SSet.const v := by
  have h : stdSimplex.δ (0 : Fin 2) ≫ lift (SSet.const v) (𝟙 (Δ[1] : SSet.{u})) =
      (SSet.const v : (Δ[0] : SSet.{u}) ⟶ _) ≫ SSet.ι₁ := by
    rw [stdSimplex.δ_zero_eq_const]
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro s
    apply Prod.ext <;> rfl
  rw [pathVertexContraction, ← Category.assoc, h, Category.assoc, pathContraction_one,
    Category.comp_id]

/-- 収縮の辺の頂点零は定数 path。 -/
lemma pathVertexContraction_face_one (Y : PointedSimplicialSet.{u})
    (v : (basedPathSpace Y).right _⦋0⦌) :
    stdSimplex.δ (1 : Fin 2) ≫ pathVertexContraction Y v =
      SSet.const (basedPathSpace Y).basepoint := by
  have h : stdSimplex.δ (1 : Fin 2) ≫ lift (SSet.const v) (𝟙 (Δ[1] : SSet.{u})) =
      (SSet.const v : (Δ[0] : SSet.{u}) ⟶ _) ≫ SSet.ι₀ := by
    rw [stdSimplex.δ_one_eq_const]
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro s
    apply Prod.ext <;> rfl
  rw [pathVertexContraction, ← Category.assoc, h, Category.assoc, pathContraction_zero,
    ← Category.assoc, comp_toUnit, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const]

/-- 概要：収縮の辺の終点は指定した path 自体の区間の射。
方針：収縮の終点評価の式に、頂点の familyMap の評価式を代入する。
規約：実際の単体集合の射の一致。
使われ方：Goerss–Jardine I §7–8。零 loop 比較の入力の辺の同定。 -/
@[reassoc]
lemma pathVertexContraction_endpoint (Y : PointedSimplicialSet.{u})
    (v : (basedPathSpace Y).right _⦋0⦌) :
    pathVertexContraction Y v ≫ (pathEndpoint Y).right =
      (PointedMapping.familyMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y v).right := by
  rw [pathVertexContraction, Category.assoc, pathContraction_endpoint]
  change lift (SSet.const v) (𝟙 (Δ[1] : SSet.{u})) ≫
    (β_ (basedPathSpace Y).right (Δ[1] : SSet.{u})).hom ≫ pathEvaluation Y =
    PointedMapping.zeroSection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.right ≫
      MonoidalClosed.uncurry (SSet.yonedaEquiv.symm v ≫
        PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y)
  rw [MonoidalClosed.uncurry_natural_left, ← Category.assoc]
  have h : PointedMapping.zeroSection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.right ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.right ◁ SSet.yonedaEquiv.symm v =
      lift (SSet.const v) (𝟙 (Δ[1] : SSet.{u})) ≫
        (β_ (basedPathSpace Y).right (Δ[1] : SSet.{u})).hom := by
    rw [SSet.yonedaEquiv_symm_zero]
    rfl
  have hh := congrArg (fun t ↦ t ≫ pathEvaluation Y) h
  simp only [Category.assoc] at hh ⊢
  exact hh.symm

end
end SerrePositivity.KST.Spectra
