module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionFiniteNormalizedPowerEquiv
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootRelativeKoszul

/-! # 有限正規化δ関係の一段におけるKoszul分解と相対比較

既存の正規化関係を最高変数分離・前段商への係数変更で実根関係へ移す。
δ包との比較の追加仮定や、完備化後の完全忠実平坦性は別の工程。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)

/-- 最高変数を分離し、下位係数を前段の実正規化商へ送る標準射。 -/
def deltaDivisionNormalizedStepPolynomialMap :
    MvPolynomial (σ × Fin (N + 2)) A →+*
      MvPolynomial σ (DeltaDivisionFiniteNormalizedQuotient D d a v N) :=
  (MvPolynomial.map (Ideal.Quotient.mk
    (deltaDivisionFiniteNormalizedPresentationIdeal D d a v N))).comp
    (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingHom

/-- 下位多項式の標準包含は前段商の係数像へ移る。 -/
theorem deltaDivisionNormalizedStepPolynomialMap_inclusion
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    deltaDivisionNormalizedStepPolynomialMap D d a v N
      (relativeFreeFiniteStepInclusion N σ f) =
      MvPolynomial.C (Ideal.Quotient.mk _ f) := by
  change MvPolynomial.map _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A
    (relativeFreeFiniteStepInclusion N σ f)) = _
  rw [relativeFreeFiniteTopVariableSplitAlgEquiv_inclusion, MvPolynomial.map_C]

/-- 最高段変数は実際の新しい根変数に対応する。 -/
theorem deltaDivisionNormalizedStepPolynomialMap_top (s : σ) :
    deltaDivisionNormalizedStepPolynomialMap D d a v N
      (MvPolynomial.X (s, Fin.last (N + 1))) = MvPolynomial.X s := by
  change MvPolynomial.map _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A
    (MvPolynomial.X (s, Fin.last (N + 1)))) = _
  rw [relativeFreeFiniteTopVariableSplitAlgEquiv_X_top, MvPolynomial.map_X]

/-- 実正規化関係式の標準像は、前段商の指定係数のp乗根関係そのもの。 -/
theorem deltaDivisionNormalizedStepPolynomialMap_relation (s : σ) :
    deltaDivisionNormalizedStepPolynomialMap D d a v N
      (deltaDivisionWittNormalizedPolynomial D d a v s N) =
      deltaRootRelationFamily (p := p)
        (deltaDivisionFiniteNormalizedStepCoefficients D d a v N) s := by
  change MvPolynomial.map _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A
    (deltaDivisionWittNormalizedPolynomial D d a v s N)) = _
  rw [deltaDivisionWittNormalizedPolynomial_top_split, map_sub, map_pow,
    MvPolynomial.map_X, MvPolynomial.map_C]
  rfl

/-- 異なる有限個の最高段関係の実像は、前段商上の弱正則列。 -/
theorem deltaDivisionNormalizedStepRelation_fin_isWeaklyRegular {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial σ (DeltaDivisionFiniteNormalizedQuotient D d a v N))
      (List.ofFn fun i ↦ deltaDivisionNormalizedStepPolynomialMap D d a v N
        (deltaDivisionWittNormalizedPolynomial D d a v (s i) N)) := by
  simpa only [deltaDivisionNormalizedStepPolynomialMap_relation] using
    deltaRootRelation_fin_isWeaklyRegular (p := p)
      (deltaDivisionFiniteNormalizedStepCoefficients D d a v N) s hs

/-- 同じ実関係像の有限Koszul複体は、その実通常商の分解となる。 -/
theorem deltaDivisionNormalizedStepRelation_fin_isKoszulResolution {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i ↦ deltaDivisionNormalizedStepPolynomialMap D d a v N
      (deltaDivisionWittNormalizedPolynomial D d a v (s i) N)) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  exact deltaDivisionNormalizedStepRelation_fin_isWeaklyRegular D d a v N s hs

/-- 前段商の任意係数加群と任意有限係数列を伴う実相対添加写像は擬同型。 -/
theorem deltaDivisionNormalizedStepRelativeKoszulAugmentation_quasiIso {m k : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s)
    (M : Type u) [AddCommGroup M] [Module (DeltaDivisionFiniteNormalizedQuotient D d a v N) M]
    (c : Fin k → DeltaDivisionFiniteNormalizedQuotient D d a v N) :
    QuasiIso (deltaRootFiniteRelativeKoszulAugmentation (p := p)
      (deltaDivisionFiniteNormalizedStepCoefficients D d a v N) s hs M c) :=
  deltaRootFiniteRelativeKoszulAugmentation_quasiIso _ s hs M c

end SerrePositivity.BhattScholze
