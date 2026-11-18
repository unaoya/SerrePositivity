module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NegativeExtendLeftAdjoint
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# 元の正規化鎖関手の小さい余極限保存

概要：元の正規化関手は小さい図式の余極限を保存する。
方針：線形化の点ごとの保存、実 Dold–Kan 同値、元の延長の左随伴性を合成。
規約：小さい単体集合から任意宇宙の係数複体への元の関手を保つ。
使われ方：実 latching 余極限と正規化境界の比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable (A : Type u) [CommRing A]

lemma normalizedFunctor_preservesSmallColimits :
    PreservesColimitsOfSize.{0, 0} (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A) := by
  let := (ModuleCat.adj A).isLeftAdjoint
  let := _root_.SerrePositivity.ComplexLimits.negativeExtend_isLeftAdjoint A
  have : (AlgebraicTopology.normalizedMooreComplex (ModuleCat.{u} A)).IsLeftAdjoint :=
    (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat.{u} A) ≌
      ChainComplex (ModuleCat.{u} A) ℕ).toAdjunction.isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} (_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A) := by
    change PreservesColimitsOfSize.{0, 0}
      ((Functor.whiskeringRight _ _ _).obj (uliftFunctor.{u, 0} ⋙ ModuleCat.free A))
    infer_instance
  change PreservesColimitsOfSize.{0, 0}
    (_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A ⋙ AlgebraicTopology.normalizedMooreComplex (ModuleCat.{u} A) ⋙
      ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A))
  infer_instance

end SerrePositivity.ComplexLimits
