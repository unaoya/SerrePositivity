module

public import SerrePositivity.InfinityCategories.F1.CocartesianOneBoundaryLocalRestrictions

/-!
概要：任意の底への全有限次元セルで、元の全 Hom の標準境界制限を揃える。
方針：標準境界包含自身の単射性を、両反変 Hom 図式の充填性へ渡す。
規約：底へのセル写像の単射性や同値性を追加仮定しない。
使われ方：高次セルの指定境界値を固定した比較の厳密補正と fiber。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (n : ℕ)
  (σ : (Δ[n + 1] : SSet.{u}) ⟶ nerve C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 同じ元のセルの全 native Hom から、標準境界への制限。 -/
def cocartesianSimplexLocalBoundarySourceRestriction :=
  ((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
    SSet.uliftFunctor.{u + 1, u}).map (boundarySimplexOverMap n σ).op

/-- 同じ元のセルの分類先 Hom から、標準境界への制限。 -/
def cocartesianSimplexLocalBoundaryTargetRestriction :=
  ((uliftOverFunctor (nerve C)).op ⋙
    intervalDiagramOverFunctor (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom)).map
        (boundarySimplexOverMap n σ).op

/-- 全次元で元の native 境界制限は Kan fibration。 -/
instance cocartesianSimplexLocalBoundarySourceRestriction_fibration :
    Fibration (cocartesianSimplexLocalBoundarySourceRestriction n σ p q) := by
  have : Mono (boundarySimplexOverMap n σ).left := inferInstanceAs (Mono (boundary (n + 1)).ι)
  exact cocartesianPullbackNativeLiftPre_fibration p.val.hom q.val.hom (boundarySimplexOverMap n σ)

/-- 全次元で元の分類先の境界制限も Kan fibration。 -/
instance cocartesianSimplexLocalBoundaryTargetRestriction_fibration :
    Fibration (cocartesianSimplexLocalBoundaryTargetRestriction n σ p q) := by
  have : Mono (boundarySimplexOverMap n σ).left := inferInstanceAs (Mono (boundary (n + 1)).ι)
  have : Mono (uliftOverMorphism.{u, u + 1} (boundarySimplexOverMap n σ)).left :=
    SimplicialModel.UniverseLift.mono_map (boundarySimplexOverMap n σ).left
  exact intervalDiagramOverPre_fibration _ _ (uliftOverMorphism (boundarySimplexOverMap n σ))

/-- 一次元で、構成した同じ source 制限は既存の両端制限そのもの。 -/
lemma cocartesianSimplexLocalBoundarySourceRestriction_zero
    (τ : (Δ[1] : SSet.{u}) ⟶ nerve C) :
    cocartesianSimplexLocalBoundarySourceRestriction 0 τ p q =
      cocartesianOneBoundaryLocalSourceRestriction τ p q := rfl

/-- 一次元で、構成した同じ target 制限も既存の両端制限そのもの。 -/
lemma cocartesianSimplexLocalBoundaryTargetRestriction_zero
    (τ : (Δ[1] : SSet.{u}) ⟶ nerve C) :
    cocartesianSimplexLocalBoundaryTargetRestriction 0 τ p q =
      cocartesianOneBoundaryLocalTargetRestriction τ p q := rfl

end SerrePositivity.InfinityCategories
