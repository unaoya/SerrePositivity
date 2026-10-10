module

public import SerrePositivity.Asymptotic.CompletedRankEvaluation
public import SerrePositivity.Asymptotic.KoszulTower

/-! # 完備化した商での Koszul 係数公式 -/

@[expose] public section

universe u

set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open CategoryTheory.Pretriangulated Filter

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}

/-- 有界自由複体列からランク商の冪等完備化への標準関手。 -/
noncomputable abbrev completedSequenceFunctor :
    SequenceHomotopy R s ⥤ CompletedSequenceRankQuotient R s :=
  sequenceRankQuotientFunctor ⋙ toKaroubi _

variable {e : ℕ} (z : Fin e → R)

/-- 商の完備化で支持される複体列を支持部分圏の対象として見る。 -/
noncomputable abbrev completedComplexObj (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex _ K)
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK))) :
    (supportedCompletedRankQuotient (s := s) z).FullSubcategory :=
  ⟨completedSequenceFunctor.obj (sequenceHomotopyObj K hK), h⟩

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 零となるスカラーに沿って反復した実際の Koszul 複体のホモロジー長。 -/
lemma completedRankBetti_sequenceKoszul_pow {n : ℕ} (x : Fin n → R)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
    (hx : ∀ j, x j • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
    (q : ℤ) :
    completedRankBetti lam hfg z hJ hfin U hU hs
      (completedComplexObj z (sequenceKoszul x K) (sequenceKoszul_bounded x K hK)
        (sequenceKoszul_map_supported completedSequenceFunctor z x K hK h)) q =
      ((cochainLengthShift + 1) ^ n)
        (completedRankBetti lam hfg z hJ hfin U hU hs (completedComplexObj z K hK h)) q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
      let P := sequenceKoszul (Fin.init x) K
      let hP := sequenceKoszul_bounded (Fin.init x) K hK
      let c := x (Fin.last n)
      let T := sequenceConeTriangle (c • 𝟙 P) hP hP
      let F := completedSequenceFunctor (R := R) (s := s)
      have hT := F.map_distinguished T (sequenceConeTriangle_distinguished _ _ _)
      have hp := sequenceKoszul_map_supported F z (Fin.init x) K hK h
      have hp' := sequenceKoszul_map_supported F z x K hK h
      let T' := fullSubcategoryTriangle (supportedCompletedRankQuotient z)
        (F.mapTriangle.obj T) hp hp hp'
      have hc := sequenceKoszul_map_smul_zero F (Fin.init x) K hK
        (fun j ↦ hx j.castSucc) c (hx (Fin.last n))
      have hf : T'.mor₁ = 0 := by
        apply ObjectProperty.hom_ext
        change F.map (show sequenceHomotopyObj P hP ⟶ sequenceHomotopyObj P hP from
          (sequenceConeTriangle (c • 𝟙 P) hP hP).mor₁) = 0
        rw [sequenceConeTriangle_smul_mor₁, F.map_smul, F.map_id]
        exact hc
      have he := completedRankBetti_zero_cone lam hfg z hJ hfin U hU hs T'
        (fullSubcategoryTriangle_distinguished _ _ _ _ _ hT) hf q
      change completedRankBetti lam hfg z hJ hfin U hU hs T'.obj₃ q = _
      rw [he]
      change completedRankBetti lam hfg z hJ hfin U hU hs
        (completedComplexObj z P hP hp) q +
          completedRankBetti lam hfg z hJ hfin U hU hs
            (completedComplexObj z P hP hp) (q + 1) = _
      rw [ih (Fin.init x) (fun j ↦ hx j.castSucc) q,
        ih (Fin.init x) (fun j ↦ hx j.castSucc) (q + 1)]
      rw [pow_succ', Module.End.mul_apply]
      simp only [LinearMap.add_apply, cochainLengthShift_apply, Module.End.one_apply,
        Pi.add_apply, add_comm]

/-- 公式 (4.2) の cochain 次数での二項係数部分。 -/
lemma completedRankBetti_sequenceKoszul {n : ℕ} (x : Fin n → R)
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
    (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
    (hx : ∀ j, x j • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
    (q : ℤ) :
    completedRankBetti lam hfg z hJ hfin U hU hs
      (completedComplexObj z (sequenceKoszul x K) (sequenceKoszul_bounded x K hK)
        (sequenceKoszul_map_supported completedSequenceFunctor z x K hK h)) q =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        completedRankBetti lam hfg z hJ hfin U hU hs (completedComplexObj z K hK h) (q + j) := by
  let y : ℕ → R := fun k ↦ if hk : k < n then x ⟨k, hk⟩ else 0
  have hy : (fun j : Fin n ↦ y j) = x := by funext j; simp [y, j.isLt]
  let X := sequenceKoszulTowerObj completedSequenceFunctor z y K hK h
  let T := sequenceKoszulTowerTriangle completedSequenceFunctor z y K hK h
  let H := completedRankHomology lam hfg z hJ hfin U hU hs 0
  have hT := sequenceKoszulTower_zero_triangles completedSequenceFunctor z y K hK h n
    (fun j hj ↦ by simpa [y, hj] using hx ⟨j, hj⟩)
  have he := iteratedZeroCone_length_binomial X (fun k ↦ (T k).mor₂)
    (fun k ↦ (T k).mor₃) n hT H (lengthQuotientValue lam s U hU hs)
    (lengthQuotientValue_add lam s U hU hs) q
  have hval (k : ℕ) (i : ℤ) :
      lengthQuotientValue lam s U hU hs ((H.shift i).obj (X k)) =
        completedRankBetti lam hfg z hJ hfin U hU hs (X k) i :=
    lengthQuotientValue_iso lam s U hU hs
      ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs i).app (X k))
  rw [hval] at he
  have hleft : completedRankBetti lam hfg z hJ hfin U hU hs (X n) q =
      completedRankBetti lam hfg z hJ hfin U hU hs
        (completedComplexObj z (sequenceKoszul x K) (sequenceKoszul_bounded x K hK)
          (sequenceKoszul_map_supported completedSequenceFunctor z x K hK h)) q := by
    change completedRankBetti lam hfg z hJ hfin U hU hs
      (completedComplexObj z (sequenceKoszul (fun j : Fin n ↦ y j) K) _ _) q = _
    simp only [hy]
  rw [← hleft, he]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact hval 0 (q + j)

end SerrePositivity.Asymptotic
