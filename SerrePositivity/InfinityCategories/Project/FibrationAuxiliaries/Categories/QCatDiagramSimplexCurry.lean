module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QCatDiagramArrowCurry

/-!
概要：単体と底の積上の同じ Cat∞ 値図式を、底上の関手の単体族へ移す。
方針：同じ二変数の射列で前合成し、元の関手空間の curry を使う。
規約：全頂点と全高次パラメーターで元の制限を回収する。
使われ方：元の比較三角形を関手空間内の同じ二単体へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 単体の射列と底の射列を、同じ積上の射列にする。 -/
def qCatDiagramSimplexProductBase (n : ℕ) (C : Type u) [Category.{u} C] :
    (Δ[n] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Fin (n + 1) × C)) where
  app _ := ↾fun ⟨α, σ⟩ ↦
    ULift.up ((SimplexCategory.toCat.map α.down).toFunctor.prod' σ.down)
  naturality _ _ _ := rfl

/-- 同じ単体と底の積上の図式を、底上の関手空間の単体族にする。 -/
def qCatDiagramSimplexCurry (n : ℕ) (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Fin (n + 1) × C))) ⟶
      (ihom (Δ[n] : SSet.{u + 1})).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))) :=
  (pre ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (Δ[n] : SSet.{u + 1})).hom ≫
    qCatDiagramSimplexProductBase n C)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) Δ[n] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u}

/-- 元の単体の頂点と底の同じ対象を組にする端点包含。 -/
def qCatDiagramSimplexEndpointIndex {n : ℕ} (i : Fin (n + 1)) (C : Type u) [Category.{u} C] :
    C ⥤ Fin (n + 1) × C where
  obj c := (i, c)
  map f := (𝟙 i, f)

/-- 同じ単体族の各頂点は、元の積上の図式の同じ頂点制限。 -/
lemma qCatDiagramSimplexCurry_endpoint (n : ℕ) (C : Type u) [Category.{u} C] (i : Fin (n + 1)) :
    qCatDiagramSimplexCurry n C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) =
      (pre ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (qCatDiagramSimplexEndpointIndex i C)))).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} := by
  apply SSet.hom_ext
  intro m
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro r α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
