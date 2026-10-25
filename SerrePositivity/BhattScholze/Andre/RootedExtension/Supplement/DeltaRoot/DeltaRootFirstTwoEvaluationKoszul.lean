module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionFiniteEvaluationRegular
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.DeltaRoot.DeltaRootSecondRelationRegular

/-! # 一元根添加の深さ≤1評価関係の実Koszul分解

実δ関係の深さ1の非零因子性を、実評価列のKoszul分解と有限源商のTorへ接続する。
全δ深さの分解や完備化後の平坦性とは区別する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "I₀" => deltaDivisionFiniteRelationIdeal E₀ (MvPolynomial.C d) c₀
local notation "g₀" => deltaDivisionIteratedRelation E₀ (MvPolynomial.C d) c₀ (default : σ)
local notation "h₀" => deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ (default : σ)

private theorem first_two_regular
    (hg : IsSMulRegular (L₀ ⧸ I₀ 0) (Ideal.Quotient.mk (I₀ 0) (g₀ 1))) :
    RingTheory.Sequence.IsWeaklyRegular L₀ (List.ofFn fun i : Fin 2 => h₀ i.val) := by
  rw [List.ofFn_succ', List.concat_eq_append,
    RingTheory.Sequence.isWeaklyRegular_append_iff]
  refine ⟨?_, ?_⟩
  · have h := deltaRootFirstEvaluation_fin_isWeaklyRegular D d b
      (fun _ : Fin 1 => (default : σ)) (fun _ _ _ => Subsingleton.elim _ _)
    simpa only [List.ofFn_succ, List.ofFn_zero, Fin.val_castSucc, Fin.val_zero] using h
  · rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    have hI : (Ideal.ofList (List.ofFn fun i : Fin 1 => h₀ i.val) • ⊤ :
        Submodule L₀ L₀) = I₀ 0 := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top,
        deltaDivisionFiniteEvaluation_ofList E₀ (MvPolynomial.C d) c₀ 0]
    change IsSMulRegular (L₀ ⧸
      (Ideal.ofList (List.ofFn fun i : Fin 1 => h₀ i.val) • ⊤ : Submodule L₀ L₀)) (h₀ 1)
    rw [hI]
    exact (isSMulRegular_map (Ideal.Quotient.mk (I₀ 0)) (fun _ => rfl)).mp
      (deltaDivisionFiniteEvaluation_next_isSMulRegular E₀ (MvPolynomial.C d) c₀ 0 hg)

/-- φ(d)正則な一般dの一元根添加では、深さ≤1の実評価列が弱正則。 -/
theorem deltaRootFirstTwoEvaluation_isWeaklyRegular
    (hd : IsSMulRegular A (D.frobeniusLift d)) :
    RingTheory.Sequence.IsWeaklyRegular L₀ (List.ofFn fun i : Fin 2 => h₀ i.val) :=
  first_two_regular D d b (deltaRootSecondRelation_isSMulRegular D d b default hd)

/-- 一元根添加の深さ≤1の実評価Koszul複体は、実通常商の分解。 -/
theorem deltaRootFirstTwoEvaluation_isKoszulResolution
    (hd : IsSMulRegular A (D.frobeniusLift d)) :
    SerrePositivity.IsKoszulResolution (fun i : Fin 2 => h₀ i.val) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaRootFirstTwoEvaluation_isWeaklyRegular D d b hd)

/-- 一元根添加の深さ≤1の実有限源グラフ商は、実自由δ射に沿う正次数Torが零。 -/
theorem deltaRootFirstTwoEvaluation_source_tor_subsingleton
    (hd : IsSMulRegular A (D.frobeniusLift d)) (i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg
      (deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)) (i + 1)
      (DeltaDivisionSourceFiniteCoordinateQuotient E₀ c₀
        (fun j : Fin 2 => (default, j.val)))) := by
  exact deltaDivisionSourceFiniteCoordinate_tor_subsingleton E₀ (MvPolynomial.C d) c₀
    (fun j : Fin 2 => (default, j.val))
    (fun _ _ hij => Fin.ext (congrArg Prod.snd hij))
    (deltaRootFirstTwoEvaluation_isKoszulResolution D d b hd) i

/-- 完全prism上では、追加の係数正則性なしに一元根添加の深さ≤1評価列がKoszul分解を与える。 -/
theorem deltaRootFirstTwoEvaluation_isKoszulResolution_of_perfectPrism
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) :
    SerrePositivity.IsKoszulResolution (fun i : Fin 2 =>
      deltaDivisionEvaluationRelation (polynomialRankOneDeltaStructure σ P.deltaStructure)
        (MvPolynomial.C P.generator) (deltaRootRelationFamily (p := p) b) default i.val) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (first_two_regular P.deltaStructure P.generator b
      (deltaRootSecondRelation_isSMulRegular_of_perfectPrism b P hP default))

/-- 完全prismからの一元根添加では、深さ≤1の実有限源商の全正次数Torが零。 -/
theorem deltaRootFirstTwoEvaluation_source_tor_subsingleton_of_perfectPrism
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg
      (deltaDivisionSourceMap (σ := σ) (polynomialRankOneDeltaStructure σ P.deltaStructure)
        (MvPolynomial.C P.generator)) (i + 1)
      (DeltaDivisionSourceFiniteCoordinateQuotient
        (polynomialRankOneDeltaStructure σ P.deltaStructure)
        (deltaRootRelationFamily (p := p) b) (fun j : Fin 2 => (default, j.val)))) := by
  exact deltaDivisionSourceFiniteCoordinate_tor_subsingleton
    (polynomialRankOneDeltaStructure σ P.deltaStructure) (MvPolynomial.C P.generator)
    (deltaRootRelationFamily (p := p) b) (fun j : Fin 2 => (default, j.val))
    (fun _ _ hij => Fin.ext (congrArg Prod.snd hij))
    (deltaRootFirstTwoEvaluation_isKoszulResolution_of_perfectPrism b P hP) i

end SerrePositivity.BhattScholze
