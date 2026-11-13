module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeReduction
public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorH0
public import SerrePositivity.HomologicalAlgebra.RegularRelationCompletedBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RegularQuotientH0

/-!
# 正則列の完備通常テンソル環の正則性

## 概要
lci 分類射の完備通常テンソル環で、基底生成元の正則性と剰余の有界性を証明する。

## 方針
正則列の商の完全平坦な底変換へ導来源を移し、その零次を通常の完備テンソル環と比較する。

## 規約
BS 著者版 Example 7.9 と D76。p 冪ねじれの有界性は関係の商に仮定する。

## 使われ方
条件付きの包絡の普遍性を一般の正則列に適用する。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward false

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open CategoryTheory CategoryTheory.Limits DerivedCompletion

attribute [local instance] HasDerivedCategory.standard

variable {p : ℕ} [Fact p.Prime] {A₀ A S : Type u} [CommRing A₀] [CommRing A]
variable (P₀ : OrientedPrism p A₀) (P : OrientedPrism p A) {r : ℕ} (f : Fin r → A)
variable (index : Fin r ≃ S)
variable (g : OrientedPrism.Hom P₀ P)

local notation "U" => RelativeFreeDeltaRing («R» := A₀) S
local notation "C" => (MvPolynomial.C : A₀ →+* U)
local notation "a" => C P₀.generator
local notation "I" => (Ideal.span {a} : Ideal U)
local notation "q" => Ideal.Quotient.mk I
local notation "c" => relativeFreeDeltaEval P.deltaStructure g.toRingHom (fun s : S => f (index.symm s))
local notation "A₁" => A ⧸ Ideal.map c I
local notation "c₀" => Ideal.quotientMap («I» := I) (Ideal.map c I) c (Ideal.le_comap_map («I» := I) (f := c))
local notation "z" => (fun i : Fin r => q (MvPolynomial.X (index i, 0)))
local notation "J" => Ideal.span (Set.range z)
local notation "T" => (U ⧸ I) ⧸ J
local notation "qz" => Ideal.Quotient.mk J
local notation "E" => completedFreeDelta P₀ S
local notation "j" => pdCompletionUnit U p a
local notation "α" => rawVariableEnvelopeMap P₀ S
local notation "K" => (Ideal.span {a} : Ideal U) ⊔
  Ideal.span (Set.range fun s : S => MvPolynomial.X (s, 0))

set_option maxHeartbeats 800000 in
/-- 概要：正則列の分類射に沿う完備通常テンソル環の生成元は正則で、その剰余の p ねじれは有界。
方針：有界な関係商への完備平坦底変換の純性を、同じ通常環の H⁰ 比較で移す。
規約：BS 著者版 Example 7.9。台環の p 正則性は仮定しない。
使われ方：一般の正則列の prismatic envelope を作る。 -/
theorem exists_lciRelation_regular_completedTensor
    (hP₀ : IsBoundedPrism P₀)
    (hd : g.toRingHom P₀.generator = P.generator)
    (hp₀ : Function.Injective (fun x : A₀ => (p : A₀) * x))
    (hpd₀ : Function.Injective (fun x : A₀ ⧸ P₀.ideal => (p : A₀ ⧸ P₀.ideal) * x))
    (hf : IsKoszulResolution (fun i => Ideal.Quotient.mk P.ideal (f i)))
    (hR : ∃ N : ℕ, ∀ (n : ℕ) (x : A ⧸ (P.ideal ⊔ Ideal.span (Set.range f))),
      (p : A ⧸ (P.ideal ⊔ Ideal.span (Set.range f))) ^ n * x = 0 →
        (p : A ⧸ (P.ideal ⊔ Ideal.span (Set.range f))) ^ N * x = 0) :
    ∃ Q : OrientedPrism p E, Q.generator = j a ∧
      IsPrismaticEnvelope P₀ (relativeFreeDeltaStructure S P₀.deltaStructure) C
        (relativeFreeDeltaStructure_C_isDeltaHom S P₀.deltaStructure) K
        ((show Ideal.span {a} ≤ K from le_sup_left) (Ideal.subset_span (Set.mem_singleton _)))
        Q α ∧
      (letI := (α).toAlgebra
       letI := (c).toAlgebra
       let H := PrismCompletedTensor (A := U) («C» := A) Q
       let l : E →+* H := prismCompletedTensorLeft Q
       IsRegular (l Q.generator) ∧
         ∃ N : ℕ, ∀ (n : ℕ) (x : H ⧸ Ideal.span {l Q.generator}),
           (p : H ⧸ Ideal.span {l Q.generator}) ^ n * x = 0 →
             (p : H ⧸ Ideal.span {l Q.generator}) ^ N * x = 0) := by
  let := pdCompletionCommRing U p a
  obtain ⟨Q, hgen, hEnv⟩ := isPrismaticEnvelope_rawVariableMap P₀ S
    (completedFreeDelta_generator_regular P₀ hP₀ S)
  change Q.generator = j a at hgen
  have hdata := exists_lciRelation_generatorReduction P₀ P f index g hd hp₀ hpd₀ hf hR
  let ReductionData (d : E) : Prop := ∃ b : T →+* E ⧸ Ideal.span {d},
      (Ideal.Quotient.mk (Ideal.span {d})).comp α = ((b).comp qz).comp q ∧
      IsCompletelyFlat (Ideal.span {(p : T)}) (baseChangeScalarModule b) ∧
      IsKoszulResolution z ∧ IsKoszulResolution (c₀ ∘ z) ∧
      ∃ N : ℕ, ∀ (n : ℕ) (x : A₁ ⧸ Ideal.map c₀ J),
        (p : A₁ ⧸ Ideal.map c₀ J) ^ n * x = 0 →
          (p : A₁ ⧸ Ideal.map c₀ J) ^ N * x = 0
  have hdata₀ : ReductionData (j a) := hdata
  have hdata' : ReductionData Q.generator := Eq.mp (congrArg ReductionData hgen.symm) hdata₀
  obtain ⟨b, hsq, hflat, hz, hf₀, hR₀⟩ := hdata'
  have ha : IsSMulRegular U a :=
    (show IsSMulRegular A₀ P₀.generator from P₀.generator_regular).of_flat (S := U)
  have hca : c a = P.generator := by rw [relativeFreeDeltaEval_C, hd]
  have hc : IsSMulRegular A (c a) := by
    rw [hca]
    exact P.generator_regular
  let X := boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule c)
  let Z := (boundedAboveDerivedCompletionFunctor E Q.generator).obj
    ((boundedAboveDerivedCompletionFunctor E (p : E)).obj
      ((boundedAboveDerivedBaseChange α).obj X))
  have hpure := completedRegularRelationBaseChange_pure_regular α c a Q.generator z b
    hsq ha hc hz hf₀ p Q.generator_regular hflat hR₀
  have hred := completedRegularRelationReduction_pure_bounded α c a Q.generator z b
    hsq ha hc hz hf₀ p Q.generator_regular hflat hR₀
  let := (α).toAlgebra
  let := (c).toAlgebra
  let H := PrismCompletedTensor (A := U) («C» := A) Q
  let l : E →+* H := prismCompletedTensorLeft Q
  let := l.toAlgebra
  let eM := baseChangeScalarAlgebraEquiv («R» := U) (B := A)
  let F := boundedAboveDerivedBaseChange α ⋙ boundedAboveDerivedCompletionFunctor E (p : E) ⋙
    boundedAboveDerivedCompletionFunctor E Q.generator
  let eZ := F.mapIso (boundedAboveDerivedSingleFunctor.mapIso eM.toModuleIso)
  let eH : (DerivedCategory.homologyFunctor (ModuleCat E) 0).obj Z.obj ≃ₗ[E] H :=
    ((DerivedCategory.homologyFunctor (ModuleCat E) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso eZ)).toLinearEquiv.trans
      (pairCompletedBaseChangeH0LinearEquiv (A := U) («C» := A) Q)
  have hleft : Function.Injective (fun x : H => l Q.generator * x) := by
    intro x y hxy
    apply eH.symm.injective
    apply hpure.2.2
    change Q.generator • eH.symm x = Q.generator • eH.symm y
    rw [← eH.symm.map_smul, ← eH.symm.map_smul]
    exact congrArg eH.symm hxy
  have hregular : IsRegular (l Q.generator) :=
    ⟨hleft, fun x y h => hleft (by simpa only [mul_comm] using h)⟩
  have hbound := boundedTorsion_quotient_of_pure_regular_reduction l Q.generator
    Q.generator_regular Z hpure.1 hpure.2.1 hpure.2.2 eH p hred.2.2
  refine ⟨Q, hgen, hEnv, hregular, ?_⟩
  have hI : (Ideal.span {Q.generator}).map l = Ideal.span {l Q.generator} := by
    rw [Ideal.map_span, Set.image_singleton]
  let Bound (JH : Ideal H) : Prop := ∃ N : ℕ, ∀ (n : ℕ) (x : H ⧸ JH),
    (p : H ⧸ JH) ^ n * x = 0 → (p : H ⧸ JH) ^ N * x = 0
  change Bound (Ideal.span {l Q.generator})
  exact Eq.mp (congrArg Bound hI) hbound

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Ex 7.9" (partial := component) "BS-W15 K5（11-11）：envelope の側は本体（R の有界性を仮定する原典の形、D76。結論は有界な prism）。p 反転の議論 G-A3-7 の古典的な入力（余法加群、分冪の像の稠密性）も本体。Δ_R/A との同一視と HT 比較の適用は drafts の A3/LciAndQuasiregular"] _root_.SerrePositivity.BhattScholze.Prismatic.exists_lciRelation_regular_completedTensor
