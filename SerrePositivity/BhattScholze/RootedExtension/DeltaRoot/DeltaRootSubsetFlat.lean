module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootSubsetQuotient
public import SerrePositivity.BhattScholze.RootedExtension.MonicPowerFamilyPolynomialFlat

/-! # 部分根関係の商の標準係数射に関する自由性・忠実平坦性

任意添字集合と零係数環を含む。実完備化後の完全忠実平坦性は別工程。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A : Type u} [CommRing A] {σ : Type v}
variable (T : Set σ) (b : σ → A)

/-- 部分根関係の商表示は標準A代数構造と両立する。 -/
def deltaRootSubsetQuotientAlgEquiv :
    (MvPolynomial σ A ⧸ deltaRootSubsetRelationIdeal (p := p) T b) ≃ₐ[A]
      MvPolynomial (Tᶜ : Set σ) (MonicPowerFamilyCover p T A (fun s ↦ b s)) := by
  apply AlgEquiv.ofRingEquiv (f := deltaRootSubsetQuotientEquiv (p := p) T b)
  intro a
  exact deltaRootSubsetQuotientEquiv_C T b a

/-- 任意部分集合の根関係の商は、標準係数射でA上自由。 -/
theorem deltaRootSubsetQuotient_moduleFree [Fact p.Prime] :
    Module.Free A (MvPolynomial σ A ⧸ deltaRootSubsetRelationIdeal (p := p) T b) := by
  let := monicPowerFamilyPolynomial_moduleFree p T (Tᶜ : Set σ) A
    (fun s ↦ b s) (Fact.out : p.Prime).pos
  exact Module.Free.of_equiv (deltaRootSubsetQuotientAlgEquiv T b).symm.toLinearEquiv

/-- 任意部分集合の根関係の商は、標準係数射でA上忠実平坦。零環も含む。 -/
theorem deltaRootSubsetQuotient_moduleFaithfullyFlat [Fact p.Prime] :
    Module.FaithfullyFlat A
      (MvPolynomial σ A ⧸ deltaRootSubsetRelationIdeal (p := p) T b) := by
  let := monicPowerFamilyPolynomial_moduleFaithfullyFlat p T (Tᶜ : Set σ) A
    (fun s ↦ b s) (Fact.out : p.Prime).pos
  exact Module.FaithfullyFlat.of_linearEquiv _ _
    (deltaRootSubsetQuotientAlgEquiv T b).toLinearEquiv

/-- 部分根関係の商はA上平坦。 -/
theorem deltaRootSubsetQuotient_moduleFlat [Fact p.Prime] :
    Module.Flat A (MvPolynomial σ A ⧸ deltaRootSubsetRelationIdeal (p := p) T b) := by
  let := deltaRootSubsetQuotient_moduleFaithfullyFlat (p := p) T b
  infer_instance

end SerrePositivity.BhattScholze
