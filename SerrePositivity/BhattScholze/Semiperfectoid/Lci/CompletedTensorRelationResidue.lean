module

public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensor
public import SerrePositivity.CommutativeAlgebra.TensorProduct.QuotientFactor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletionResidue
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionLinearMap
import all SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensor
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 完備テンソル積の剰余と関係商上のテンソル

## 概要
prism の生成元剰余を、そこで零になる関係を基底と係数から除いたテンソルの実 p 完備化へ比較する。
## 方針
二座標完備化の剰余比較と、通常のテンソルの関係商比較を合成する。
## 規約
BS 著者版 Example 7.9・Proposition 7.10。単位の対応式を返す。
## 使われ方
有限 T の包絡の完全忠実平坦性。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic
open _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {U A E : Type u}
  [CommRing U] [CommRing A] [CommRing E] [Algebra U A] [Algebra U E]

/-- 完備テンソルの剰余を、関係商上の通常テンソルの実完備化へ、右係数の単位を保って比較する。 -/
theorem _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_prismCompletedTensor_relationResidue_equiv (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p E)
    (K : Ideal U) (hK : K.map (algebraMap U E) ≤ Q.ideal) :
    letI := _root_.SerrePositivity.quotientFactorAlgebra U E K Q.ideal hK
    letI := _root_.SerrePositivity.adicQuotientAlgebra K A
    let V := (A ⧸ K.map (algebraMap U A)) ⊗[U ⧸ K] (E ⧸ Q.ideal)
    let H := _root_.SerrePositivity.BhattScholze.PrismCompletedTensor (A := U) (C := A) Q
    ∃ e : (H ⧸ Ideal.span {_root_.SerrePositivity.BhattScholze.prismCompletedTensorLeft Q Q.generator}) ≃+* CompletedRing p V,
      ∀ a : A, e (Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.prismCompletedTensorRight Q a)) =
        (principalCompletionRingCatUnit p (CommRingCat.of V)).hom
          (Ideal.Quotient.mk _ a ⊗ₜ[U ⧸ K] (1 : E ⧸ Q.ideal)) := by
  letI := _root_.SerrePositivity.quotientFactorAlgebra U E K Q.ideal hK
  letI := _root_.SerrePositivity.adicQuotientAlgebra K A
  let V := (A ⧸ K.map (algebraMap U A)) ⊗[U ⧸ K] (E ⧸ Q.ideal)
  let T := E ⊗[U] A
  let d : T := algebraMap E T Q.generator
  let J := Q.ideal.map (algebraMap E T)
  have hJ : J = Ideal.span {d} := by
    change (Ideal.span {Q.generator}).map (algebraMap E T) = _
    rw [Ideal.map_span, Set.image_singleton]
  let eV : (T ⧸ Ideal.span {d}) ≃+* V :=
    (Ideal.quotEquivOfEq hJ.symm).trans (_root_.SerrePositivity.tensorQuotientFactorEquiv U A E K Q.ideal hK)
  letI := pdCompletionCommRing T p d
  letI := principalCompletionCommRing (T ⧸ Ideal.span {d}) (p : T ⧸ Ideal.span {d})
  letI := principalCompletionCommRing V (p : V)
  let e0 := pdCompletionResidueEquiv T p d
  let e1 := principalCompletionRingEquiv eV (p : T ⧸ Ideal.span {d}) (p : V) (map_natCast eV p)
  refine ⟨e0.trans e1, fun a => ?_⟩
  change e1 (e0 (Ideal.Quotient.mk _ (pdCompletionUnit T p d ((1 : E) ⊗ₜ[U] a)))) = _
  rw [pdCompletionResidueEquiv_unit, principalCompletionRingEquiv_unit]
  have hv : eV (Ideal.Quotient.mk _ ((1 : E) ⊗ₜ[U] a)) =
      Ideal.Quotient.mk _ a ⊗ₜ[U ⧸ K] (1 : E ⧸ Q.ideal) := by
    change _root_.SerrePositivity.tensorQuotientFactorEquiv U A E K Q.ideal hK
      (Ideal.Quotient.mk _ ((1 : E) ⊗ₜ[U] a)) = _
    simpa only [map_one] using _root_.SerrePositivity.tensorQuotientFactorEquiv_tmul U A E K Q.ideal hK (1 : E) a
  rw [hv]
  rfl

end SerrePositivity.BhattScholze.Prismatic
