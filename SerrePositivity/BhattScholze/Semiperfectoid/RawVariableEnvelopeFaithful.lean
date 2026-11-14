module

public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.LciEnvelopeCompletedResidueFaithful
public import SerrePositivity.BhattScholze.Semiperfectoid.CompletedTensorRelationFaithful
public import SerrePositivity.BhattScholze.Semiperfectoid.RawVariableEnvelope

/-!
# 普遍変数包絡の関係商上の忠実性

## 概要
普遍変数包絡の生成元剰余は、元の関係商の標準作用で p 完全忠実平坦。
## 方針
既存の自由変数除算の剰余射と、実包絡の標準作用を同じ単位で照合する。
## 規約
BS 著者版 Example 7.9・Proposition 7.10。
## 使われ方
一般の有限正則関係への完備底変換。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open Prismatic DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A]
variable (P : OrientedPrism p A)
local notation "U" => RelativeFreeDeltaRing (R := A) S
local notation "a" => (MvPolynomial.C P.generator : U)
local notation "E" => completedFreeDelta P S
local notation "j" => pdCompletionUnit U p a
local notation "α" => rawVariableEnvelopeMap P S
local notation "K" => (Ideal.span {a} : Ideal U) ⊔
  Ideal.span (Set.range fun s : S => MvPolynomial.X (s, 0))

/-- 普遍変数包絡の標準剰余作用で、関係商上の p 完全忠実平坦性が成り立つ。 -/
theorem rawVariableEnvelope_residue_completelyFaithfullyFlat
    (hp : Function.Injective (fun x : A => (p : A) * x))
    (hpd : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
    (Q : OrientedPrism p E) (hgen : Q.generator = j a) (hmap : (K).map α ≤ Q.ideal) :
    letI := (α).toAlgebra
    letI := quotientFactorAlgebra U E K Q.ideal hmap
    IsCompletelyFaithfullyFlat (Ideal.span {(p : U ⧸ K)}) (E ⧸ Q.ideal) := by
  letI := pdCompletionCommRing U p a
  letI := (α).toAlgebra
  letI := quotientFactorAlgebra U E K Q.ideal hmap
  have hQL : Q.ideal = Ideal.span {j a} := by
    change Ideal.span {Q.generator} = _
    rw [hgen]
    rfl
  have hu : IsUnit (P.deltaStructure.delta P.generator) := P.isDistinguished_generator
  obtain ⟨b0, hb0, hf0⟩ := exists_completedFreeVariable_generatorResidue_completelyFaithfullyFlat
    (S := S) P.deltaStructure P.generator hp hpd hu.unit hu.unit_spec
  letI := b0.toAlgebra
  let eL : (E ⧸ Q.ideal) ≃+* E ⧸ Ideal.span {j a} := Ideal.quotEquivOfEq hQL
  let eA : (E ⧸ Q.ideal) ≃ₐ[U ⧸ K] E ⧸ Ideal.span {j a} :=
    AlgEquiv.ofRingEquiv (f := eL) (fun z => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      change eL (Ideal.Quotient.mk Q.ideal (α x)) = b0 (Ideal.Quotient.mk K x)
      rw [Ideal.quotEquivOfEq_mk, hb0]
      rfl)
  exact isCompletelyFaithfullyFlat_of_linearEquiv _ eA.symm.toLinearEquiv hf0

end SerrePositivity.BhattScholze.Semiperfectoid
