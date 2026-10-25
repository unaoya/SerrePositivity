module

public import SerrePositivity.BhattScholze.Andre.Variants.RegularQuotientCompleteFaithful
public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaAlgebra.PerfectPrismDeltaAlgebraPDCompletelyFlat
public import SerrePositivity.BhattScholze.Prism.Perfection.PerfectDeltaPDPrism
public import SerrePositivity.HomologicalAlgebra.TorAlgebraAcyclicBaseChange

/-!
# André E1・E2：完全 δ 化後の任意の同じ生成元商

## 概要

完全 δ 基底上の実剰余入力から、完全化後の生成元商の自然な射は p 完全忠実平坦。
BS Rem 7.15（著者版 p.62）の最終商への一般移送。

## 方針

二元完全忠実平坦性を正則主商へ下降し、生成元の等式で同じ商の別表記へ移す。

## 規約

原典とは異なる Tor 底変換による経路。導来剰余の離散性・忠実平坦性を明示引数とする。

## 使われ方

元の無限根モニック候補には実剰余の検証済み入力を適用する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (E : DeltaStructure p B) (j : A →+* B)
variable (hP : P.deltaStructure.IsPerfect) (hj : P.deltaStructure.IsDeltaHom E j)
variable
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) i).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj))
    (hFF : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), P.generator})
      ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) 0).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj))
local notation "C" => DeltaPerfection E
local notation "κ" => deltaAlgebraPerfectionCoefficient E j
local notation "R" => A ⧸ Ideal.span {OrientedPrism.generator P}

/-- 概要：完全化の指定生成元商への標準基底射。
方針：生成元の係数像との等式を用いて通常主商へ降ろす。
規約：商に使う元 b を明示し、生成元像と等しいことを要求する。
使われ方：BS Rem 7.15（著者版 p.62）の異なる生成元表記の照合。 -/
def perfectedDeltaAlgebraQuotientBaseMap (b : C) (hb : κ P.generator = b) :
    let := pdCompletionCommRing C p b
    R →+* (PDCompletionH0 C p b ⧸ Ideal.span {pdCompletionUnit C p b b}) := by
  let := pdCompletionCommRing C p b
  let v := pdCompletionUnit C p b
  let q := Ideal.Quotient.mk (Ideal.span {v b})
  apply Ideal.Quotient.lift (Ideal.span {P.generator}) (q.comp (v.comp κ))
  change Ideal.span {P.generator} ≤ RingHom.ker (q.comp (v.comp κ))
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  change q (v (κ P.generator)) = 0
  rw [hb]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- 概要：標準基底射は元の基底係数の像を保つ。
方針：通常主商の降下射の代表元公式。
規約：b の等式の証明の選択には依存しない。
使われ方：BS Rem 7.15（著者版 p.62）の具体的基底射の照合。 -/
theorem perfectedDeltaAlgebraQuotientBaseMap_mk (b : C) (hb : κ P.generator = b) (r : A) :
    let := pdCompletionCommRing C p b
    perfectedDeltaAlgebraQuotientBaseMap P E j b hb (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk (Ideal.span {pdCompletionUnit C p b b})
        (pdCompletionUnit C p b (κ r)) := rfl

include hP hj hzero hFF in
/-- 概要：完全化後の指定生成元商の自然な基底射は p 完全忠実平坦。
方針：生成元の等式で標準表記へ戻し、二元完全忠実平坦性を正則主商へ下降する。
規約：同じ実剰余入力と自然な基底作用を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の最終 perfectoid 候補。 -/
theorem perfectedDeltaAlgebraQuotientBaseMap_completelyFaithfullyFlat
    (b : C) (hb : κ P.generator = b) :
    let := pdCompletionCommRing C p b
    let := (perfectedDeltaAlgebraQuotientBaseMap P E j b hb).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R)})
      (PDCompletionH0 C p b ⧸ Ideal.span {pdCompletionUnit C p b b}) := by
  subst b
  let := pdCompletionCommRing C p (κ P.generator)
  let H := PDCompletionH0 C p (κ P.generator)
  let v := pdCompletionUnit C p (κ P.generator)
  let t := v.comp κ
  let : Algebra A H := t.toAlgebra
  have hk := deltaAlgebraPerfectionCoefficient_isDeltaHom P.deltaStructure E j hj
  have hd := hk.map_isDistinguished (P.isDistinguished_of_perfect hP)
  have hreg : IsSMulRegular H (algebraMap A H P.generator) :=
    (perfectDeltaPDPrism (deltaPerfectionStructure E) (deltaPerfection_isPerfect E)
      (κ P.generator) hd).generator_regular
  have hcf : IsCompletelyFaithfullyFlat (Ideal.span {(p : A), P.generator}) H :=
    isCompletelyFaithfullyFlat_of_linearEquiv _ (baseChangeScalarAlgebraEquiv (B := H))
      (perfectPrismDeltaAlgebraPD_isCompletelyFaithfullyFlat P E j hP hj hzero hFF)
  have h := completelyFaithfullyFlat_principal_quotient_of_pair p P.generator
    P.generator_regular H hreg hcf
  have ha : (perfectedDeltaAlgebraQuotientBaseMap P E j (κ P.generator) rfl).toAlgebra =
      principalAdicQuotientAlgebra P.generator H := by
    apply Algebra.algebra_ext
    intro r
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    rfl
  rw [ha]
  exact h

end SerrePositivity.BhattScholze.Andre
