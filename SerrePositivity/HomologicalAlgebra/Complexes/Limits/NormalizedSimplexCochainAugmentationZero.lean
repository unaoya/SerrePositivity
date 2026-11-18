module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexAugmentationZero

/-!
# 同じコチェイン単体 augmentation の零次数での値

概要：元の正規化単体の同じ零次数生成元は元のコチェイン augmentation により 1 へ送られる。
方針：同じ延長の項同型と一点複体の同型を相殺し、元の鎖 augmentation を評価する。
規約：元の順方向の収縮と生成元を保つ。
使われ方：正規化テンソル augmentation の curry の零次数を恒等射へ同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedSimplexCochainAugmentation_zero_apply (n : SimplexCategory)
    (w : ((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj n))).X 0) :
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom.f 0
        ((((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj n))).extendXIso
            ComplexShape.embeddingDownNat rfl).inv w)) =
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexChainContraction A n).hom.f 0 w := by
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
    ((extendSingleIso ComplexShape.embeddingDownNat (𝟙_ (ModuleCat A)) 0 0 rfl).hom.f 0
      ((extendMap (_root_.SerrePositivity.ComplexLimits.normalizedSimplexChainContraction A n).hom ComplexShape.embeddingDownNat).f 0
        ((((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj n))).extendXIso
            ComplexShape.embeddingDownNat rfl).inv w))) = _
  rw [extendSingleIso_hom_f,
    extendMap_f (_root_.SerrePositivity.ComplexLimits.normalizedSimplexChainContraction A n).hom ComplexShape.embeddingDownNat
      (i := 0) (i' := 0) rfl]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom]
  let L := (AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj n))
  change (_root_.SerrePositivity.ComplexLimits.normalizedSimplexChainContraction A n).hom.f 0
    ((L.extendXIso ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl)).hom
      ((L.extendXIso ComplexShape.embeddingDownNat
        (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl)).inv w)) = _
  exact congrArg (fun z => (_root_.SerrePositivity.ComplexLimits.normalizedSimplexChainContraction A n).hom.f 0 z)
    (ConcreteCategory.congr_hom (L.extendXIso ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl)).inv_hom_id w)

lemma normalizedSimplexCochainAugmentation_zero_generator :
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A ⦋0⦌).hom.f 0
        (_root_.SerrePositivity.ComplexLimits.normalizedSimplexZeroGenerator A)) = (1 : A) := by
  let x : (SSet.stdSimplex.obj ⦋0⦌ : SSet.{0}) _⦋0⦌ :=
    SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)
  have h := _root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainAugmentation_zero_apply A ⦋0⦌
    ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj
      (SSet.stdSimplex.obj ⦋0⦌))).inv (ModuleCat.freeMk (ULift.up x)))
  exact h.trans (_root_.SerrePositivity.ComplexLimits.normalizedSimplexChainAugmentation_zero A ⦋0⦌ x)

end SerrePositivity.ComplexLimits
