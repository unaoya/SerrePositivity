module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootFiniteRegularSequence
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootSubsetFlat
public import SerrePositivity.HomologicalAlgebra.DerivedTensor
public import SerrePositivity.HomologicalAlgebra.Tor
public import SerrePositivity.HomologicalAlgebra.TorFlatBaseChangeVanishing

/-! # 有限根関係の実商の係数側Tor

標準係数射A→商についてのTorと、源多項式環への平坦係数拡大後のTorを計算する。
(p,d)のKoszul複体自体の次数零集中とは区別する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A σ : Type u} [CommRing A]
variable (b : σ → A) {n : ℕ} (s : Fin n → σ)

/-- 有限根関係の実生成イデアルは、添字の像の部分集合イデアル。 -/
theorem deltaRootFiniteRelationIdeal_eq_subset :
    Ideal.span (Set.range fun i ↦ deltaRootRelationFamily (p := p) b (s i)) =
      deltaRootSubsetRelationIdeal (p := p) (Set.range s) b := by
  unfold deltaRootSubsetRelationIdeal
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨⟨s i, ⟨i, rfl⟩⟩, rfl⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨i, hi⟩ := t.property
    exact ⟨i, congrArg (deltaRootRelationFamily (p := p) b) hi⟩

/-- 有限根関係の実商は、標準係数射によってA上平坦。添字の単射性は不要。 -/
theorem deltaRootFiniteQuotient_moduleFlat [Fact p.Prime] :
    Module.Flat A (MvPolynomial σ A ⧸
      Ideal.span (Set.range fun i ↦ deltaRootRelationFamily (p := p) b (s i))) := by
  rw [deltaRootFiniteRelationIdeal_eq_subset]
  exact deltaRootSubsetQuotient_moduleFlat (p := p) (Set.range s) b

/-- 有限根関係の実商は、標準係数射によってA上忠実平坦。零係数環も含む。 -/
theorem deltaRootFiniteQuotient_moduleFaithfullyFlat [Fact p.Prime] :
    Module.FaithfullyFlat A (MvPolynomial σ A ⧸
      Ideal.span (Set.range fun i ↦ deltaRootRelationFamily (p := p) b (s i))) := by
  rw [deltaRootFiniteRelationIdeal_eq_subset]
  exact deltaRootSubsetQuotient_moduleFaithfullyFlat (p := p) (Set.range s) b

/-- 任意係数加群Nとの高次Torは零。既存Torを具体的な有限商へ適用する。 -/
theorem deltaRootFiniteQuotient_tor_subsingleton [Fact p.Prime]
    (N : Type u) [AddCommGroup N] [Module A N] (i : ℕ) :
    Subsingleton (TorModule A (i + 1) (MvPolynomial σ A ⧸
      Ideal.span (Set.range fun i ↦ deltaRootRelationFamily (p := p) b (s i))) N) := by
  let := deltaRootFiniteQuotient_moduleFlat (p := p) b s
  exact torModule_subsingleton_of_flat _ N i

/-- 任意係数加群Nとの実導来テンソルは次数零に集中する。 -/
theorem deltaRootFiniteQuotient_derivedTensor_concentrated [Fact p.Prime]
    (N : Type u) [AddCommGroup N] [Module A N] :
    IsConcentratedInDegreeZero (derivedTensor A (MvPolynomial σ A ⧸
      Ideal.span (Set.range fun i ↦ deltaRootRelationFamily (p := p) b (s i))) N) := by
  rw [isConcentratedInDegreeZero_derivedTensor_iff]
  intro i hi
  cases i with
  | zero => exact (Nat.lt_irrefl 0 hi).elim
  | succ i => exact deltaRootFiniteQuotient_tor_subsingleton b s N i

/-- 源多項式環へ係数拡大した任意加群に対しても、実商との高次Torは零。 -/
theorem deltaRootFiniteQuotient_tor_baseChange_subsingleton [Fact p.Prime]
    (N : Type u) [AddCommGroup N] [Module A N] (i : ℕ) :
    Subsingleton (TorModule (MvPolynomial σ A) (i + 1) (MvPolynomial σ A ⧸
      Ideal.span (Set.range fun i ↦ deltaRootRelationFamily (p := p) b (s i)))
      (TensorProduct A (MvPolynomial σ A) N)) := by
  exact torModule_baseChange_subsingleton A (MvPolynomial σ A) _ N (i + 1)
    (deltaRootFiniteQuotient_tor_subsingleton (p := p) b s N i)

/-- 源多項式環上での実商と係数拡大加群の導来テンソルは次数零に集中する。 -/
theorem deltaRootFiniteQuotient_derivedTensor_baseChange_concentrated [Fact p.Prime]
    (N : Type u) [AddCommGroup N] [Module A N] :
    IsConcentratedInDegreeZero (derivedTensor (MvPolynomial σ A) (MvPolynomial σ A ⧸
      Ideal.span (Set.range fun i ↦ deltaRootRelationFamily (p := p) b (s i)))
      (TensorProduct A (MvPolynomial σ A) N)) := by
  rw [isConcentratedInDegreeZero_derivedTensor_iff]
  intro i hi
  cases i with
  | zero => exact (Nat.lt_irrefl 0 hi).elim
  | succ i => exact deltaRootFiniteQuotient_tor_baseChange_subsingleton b s N i

end SerrePositivity.BhattScholze
