module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawBaseChangeQuotient
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDModelBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TensorCompletionUnit
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.TensorCompletionUnit
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Envelopes.PDModelBaseChange
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 小さい分冪項の完備テンソル比較

## 概要
小さい分冪模型の係数変更は、各項の通常テンソルの p 完備化を計算する。

## 方針
未完備項の自由基底の底変換同型を完備化し、テンソル内の完備化単位を消す。

## 規約
この環の同型には平坦性を仮定しない。導来底変換の離散性は別に扱う。

## 使われ方
BS 著者版 Theorem 6.4、Witt 係数の二比較の各項の同定。
-/

public noncomputable section
open CategoryTheory
open scoped TensorProduct Simplicial
open SerrePositivity.DerivedCompletion
open SerrePositivity.DerivedCompletion.TensorCompletionUnit
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def completeEquiv (p : ℕ) (k R S : Type u)
    [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (e : R ≃ₐ[k] S) : CompletedRing p R ≃ₐ[k] CompletedRing p S := by
  let f := completedAlgMap p k R S e.toAlgHom
  let g := completedAlgMap p k S R e.symm.toAlgHom
  have hgf : g.comp f = AlgHom.id k (CompletedRing p R) := by
    apply AlgHom.toLinearMap_injective
    apply principalCompletionLinearMap_ext k p (completedRing_isModuleComplete k p (A := R))
    intro x
    change g (f (principalCompletionRingCatUnit p (CommRingCat.of R) x)) =
      principalCompletionRingCatUnit p (CommRingCat.of R) x
    rw [completedAlgMap_unit, completedAlgMap_unit]
    exact congrArg (principalCompletionRingCatUnit p (CommRingCat.of R)) (e.symm_apply_apply x)
  have hfg : f.comp g = AlgHom.id k (CompletedRing p S) := by
    apply AlgHom.toLinearMap_injective
    apply principalCompletionLinearMap_ext k p (completedRing_isModuleComplete k p (A := S))
    intro x
    change f (g (principalCompletionRingCatUnit p (CommRingCat.of S) x)) =
      principalCompletionRingCatUnit p (CommRingCat.of S) x
    rw [completedAlgMap_unit, completedAlgMap_unit]
    exact congrArg (principalCompletionRingCatUnit p (CommRingCat.of S)) (e.apply_symm_apply x)
  exact AlgEquiv.ofAlgHom f g hfg hgf

private theorem completeEquiv_unit (p : ℕ) (k R S : Type u)
    [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (e : R ≃ₐ[k] S) (x : R) :
    completeEquiv p k R S e (principalCompletionRingCatUnit p (CommRingCat.of R) x) =
      principalCompletionRingCatUnit p (CommRingCat.of S) (e x) :=
  completedAlgMap_unit p k R S e.toAlgHom x

variable (p : ℕ) (k l : Type u) [CommRing k] [CommRing l] [Algebra k l] (r n : ℕ)

local instance : CommRing (l ⊗[k] pdRaw k r n) :=
  @Algebra.TensorProduct.instCommRing k l (pdRaw k r n) _ _ _ _ _

/-- 完備分冪項の通常テンソルをさらに完備化すると、係数変更後の分冪項になる。 -/
def pdTermCompletedTensorAlgEquiv :
    CompletedRing p (l ⊗[k] pdTerm p k r n) ≃ₐ[l] pdTerm p l r n :=
  (completionTensorUnitAlgEquiv p k l (pdRaw k r n)).symm.trans
    (completeEquiv p l (l ⊗[k] pdRaw k r n) (pdRaw l r n)
      (pdRawCoefficients_baseChangeAlgEquiv k l r n))

/-- 未完備項の元をテンソルしたとき、比較は実際の係数変更の完備化単位を与える。 -/
theorem pdTermCompletedTensorAlgEquiv_raw (a : l) (x : pdRaw k r n) :
    pdTermCompletedTensorAlgEquiv p k l r n
        (principalCompletionRingCatUnit p (CommRingCat.of (l ⊗[k] pdTerm p k r n))
          (a ⊗ₜ[k] principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r n)) x)) =
      principalCompletionRingCatUnit p (CommRingCat.of (pdRaw l r n))
        (a • pdRawCoefficients k l r n x) := by
  have hu := completionTensorUnitEquiv_unit p k l (pdRaw k r n) (a ⊗ₜ[k] x)
  have hi : (completionTensorUnitAlgEquiv p k l (pdRaw k r n)).symm
      (principalCompletionRingCatUnit p (CommRingCat.of (l ⊗[k] pdTerm p k r n))
        (a ⊗ₜ[k] principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r n)) x)) =
      principalCompletionRingCatUnit p (CommRingCat.of (l ⊗[k] pdRaw k r n)) (a ⊗ₜ[k] x) := by
    apply (completionTensorUnitAlgEquiv p k l (pdRaw k r n)).injective
    rw [AlgEquiv.apply_symm_apply]
    exact hu.symm
  change completeEquiv p l (l ⊗[k] pdRaw k r n) (pdRaw l r n)
    (pdRawCoefficients_baseChangeAlgEquiv k l r n)
    ((completionTensorUnitAlgEquiv p k l (pdRaw k r n)).symm
      (principalCompletionRingCatUnit p (CommRingCat.of (l ⊗[k] pdTerm p k r n))
        (a ⊗ₜ[k] principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r n)) x))) = _
  rw [hi, completeEquiv_unit, pdRawCoefficients_baseChangeAlgEquiv_tmul]

/-- 既存の模型の係数変更を、二つの完備項の間の環射として読む。 -/
def pdTermCoefficientRingHom : pdTerm p k r n →+* pdTerm p l r n :=
  ((pdModelBaseChange p k l r).app ⦋n⦌).right.hom

/-- 完備項の右脚は、指定済みの小さい模型の係数変更そのものになる。 -/
theorem pdTermCompletedTensorAlgEquiv_coefficient (x : pdTerm p k r n) :
    pdTermCompletedTensorAlgEquiv p k l r n
        (principalCompletionRingCatUnit p (CommRingCat.of (l ⊗[k] pdTerm p k r n))
          (1 ⊗ₜ[k] x)) =
      pdTermCoefficientRingHom p k l r n x := by
  let f : pdTerm p k r n →+* pdTerm p l r n :=
    (pdTermCompletedTensorAlgEquiv p k l r n).toRingHom.comp
      ((principalCompletionRingCatUnit p (CommRingCat.of (l ⊗[k] pdTerm p k r n))).hom.comp
        (Algebra.TensorProduct.includeRight.toRingHom :
          pdTerm p k r n →+* l ⊗[k] pdTerm p k r n))
  let g : pdTerm p k r n →+* pdTerm p l r n :=
    ((pdModelBaseChange p k l r).app ⦋n⦌).right.hom
  let b : pdRaw k r n →+* pdTerm p l r n :=
    (principalCompletionRingCatUnit p (CommRingCat.of (pdRaw l r n))).hom.comp
      (pdRawCoefficients k l r n).toRingHom
  have hf : f.comp (principalCompletionUnitRingHom (pdRaw k r n) (p : pdRaw k r n)) = b := by
    apply RingHom.ext
    intro y
    exact (pdTermCompletedTensorAlgEquiv_raw p k l r n 1 y).trans
      (congrArg (principalCompletionRingCatUnit p (CommRingCat.of (pdRaw l r n))) (one_smul l _))
  have hg : g.comp (principalCompletionUnitRingHom (pdRaw k r n) (p : pdRaw k r n)) = b := by
    apply RingHom.ext
    intro y
    exact pdModelBaseChange_unit p k l r ⦋n⦌ y
  have hfg : f = g :=
    (principalCompletion_existsUnique_ringHom (pdRaw k r n) (p : pdRaw k r n)
      (pdTerm p l r n) b
      (TensorCompletionUnit.targetComplete p (pdRaw k r n) (pdRaw l r n) b)).unique hf hg
  exact RingHom.congr_fun hfg x

end SerrePositivity.BhattScholze.Prismatic
