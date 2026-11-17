module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantAlgebraRelativeInput
public import SerrePositivity.EInfinity.Hammock.HomLiftColimit

/-!
# 元の全代数と cofibrant DK 入力を同じ Hom の宇宙へ揃える

概要：元の全代数の Hom だけを ULift し、同じ包含・同じ cofibrant 置換を渡す。
方針：元のモデルの弱同値を down で引き戻す。
規約：対象・代数射・元の弱同値と指定置換を保持する。
使われ方：既存 CAlg_R の DK Hom と元の Map^h の hammock の比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory _root_.HomotopicalAlgebra
variable (A : Type u) [CommRing A]
def algebraRelativeCategory : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u + 1} := by
  let := modelCategory A
  exact
    { category := Cat.of (ULiftHom.{u + 1} (operad A).Algebra)
      weakEquivalences := Hammock.HomLift.liftedWeak (C := (operad A).Algebra)
        (weakEquivalences (operad A).Algebra)
      isMultiplicative := Hammock.HomLift.liftedWeak_isMultiplicative
        (C := (operad A).Algebra) (weakEquivalences (operad A).Algebra) }
def cofibrantToAlgebraDKRelative :
    cofibrantAlgebraRelativeCategory A ⟶ algebraRelativeCategory A := by
  let := modelCategory A
  exact ⟨cofibrantAlgebraDKInclusion A ⋙
    ULiftHom.up.{u, u + 1, u + 1} (C := (operad A).Algebra), fun _ _ _ hf => hf⟩
def algebraToCofibrantDKRelative :
    algebraRelativeCategory A ⟶ cofibrantAlgebraRelativeCategory A := by
  let := modelCategory A
  exact ⟨ULiftHom.down.{u, u + 1, u + 1} (C := (operad A).Algebra) ⋙
    cofibrantAlgebraDKReplacement A, fun _ _ f hf =>
      (cofibrantAlgebraDKReplacementRelative A).map f.down hf⟩
end SerrePositivity.EInfinity.BarrattEccles
