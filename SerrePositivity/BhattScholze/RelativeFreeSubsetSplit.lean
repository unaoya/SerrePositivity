module

public import SerrePositivity.BhattScholze.RelativeFreeUniversal
public import SerrePositivity.BhattScholze.DeltaDivisionIteratedRelations
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Logic.Equiv.Set

/-! # 部分根族と補集合の自由δ変数の分離 -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (T : Set σ)

/-- 各δ深さを保って、部分根族と補集合の座標を分ける添字同値。 -/
def relativeFreeSubsetVariableSplit :
    σ × ℕ ≃ (T × ℕ) ⊕ ((Tᶜ : Set σ) × ℕ) := by
  classical
  exact (Equiv.prodCongr (Equiv.Set.sumCompl T).symm (Equiv.refl ℕ)).trans
    (Equiv.sumProdDistrib T (Tᶜ : Set σ) ℕ)

/-- 部分根族の座標は外側の多項式変数へ送られる。 -/
@[simp] theorem relativeFreeSubsetVariableSplit_mem (s : T) (n : ℕ) :
    relativeFreeSubsetVariableSplit T (s, n) = Sum.inl (s, n) := by
  classical
  simp [relativeFreeSubsetVariableSplit]

/-- 補集合の座標は係数側の多項式変数へ送られる。 -/
@[simp] theorem relativeFreeSubsetVariableSplit_compl (s : (Tᶜ : Set σ)) (n : ℕ) :
    relativeFreeSubsetVariableSplit T (s, n) = Sum.inr (s, n) := by
  classical
  simp [relativeFreeSubsetVariableSplit]

local notation "B" => RelativeFreeDeltaRing (R := A) (Tᶜ : Set σ)
local notation "C" => RelativeFreeDeltaRing (R := B) T

/-- 補集合の自由δ環を係数にすると、元の自由環は部分根族の相対自由環となる。 -/
def relativeFreeSubsetSplitAlgEquiv : RelativeFreeDeltaRing (R := A) σ ≃ₐ[A] C :=
  (MvPolynomial.renameEquiv A (relativeFreeSubsetVariableSplit T)).trans
    (MvPolynomial.sumAlgEquiv A (T × ℕ) ((Tᶜ : Set σ) × ℕ))

/-- 分離同型は元の係数を二重の係数射へ送る。 -/
@[simp] theorem relativeFreeSubsetSplitAlgEquiv_C (a : A) :
    relativeFreeSubsetSplitAlgEquiv (A := A) T (MvPolynomial.C a) =
      MvPolynomial.C (MvPolynomial.C a) := by
  simp [relativeFreeSubsetSplitAlgEquiv]

/-- 部分根族の全δ座標は外側の座標となる。 -/
@[simp] theorem relativeFreeSubsetSplitAlgEquiv_X_mem (s : T) (n : ℕ) :
    relativeFreeSubsetSplitAlgEquiv (A := A) T (MvPolynomial.X ((s : σ), n)) =
      MvPolynomial.X (s, n) := by
  simp [relativeFreeSubsetSplitAlgEquiv]

/-- 補集合の全δ座標は係数環の座標となる。 -/
@[simp] theorem relativeFreeSubsetSplitAlgEquiv_X_compl (s : (Tᶜ : Set σ)) (n : ℕ) :
    relativeFreeSubsetSplitAlgEquiv (A := A) T (MvPolynomial.X ((s : σ), n)) =
      MvPolynomial.C (MvPolynomial.X (s, n)) := by
  simp [relativeFreeSubsetSplitAlgEquiv]

variable (D : DeltaStructure p A)
local notation "E" => relativeFreeDeltaStructure σ D
local notation "F" => relativeFreeDeltaStructure (Tᶜ : Set σ) D
local notation "G" => relativeFreeDeltaStructure T F
local notation "e" => relativeFreeSubsetSplitAlgEquiv (A := A) T

/-- 全δ深さを保つ部分族分離は、既存の二つの自由δ構造と両立する。 -/
theorem relativeFreeSubsetSplitAlgEquiv_isDeltaHom :
    (E).IsDeltaHom G (e).toRingHom := by
  apply (DeltaStructure.isDeltaHom_iff_sectionHom_comp _ _ _).mpr
  apply MvPolynomial.ringHom_ext
  · intro a
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · change e (((E).sectionHom (MvPolynomial.C a)).coeff 0) =
        ((G).sectionHom (e (MvPolynomial.C a))).coeff 0
      rw [(E).coeff_zero, (G).coeff_zero]
    · change e ((E).delta (MvPolynomial.C a)) = (G).delta (e (MvPolynomial.C a))
      simp
  · rintro ⟨s, n⟩
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · change e (((E).sectionHom (MvPolynomial.X (s, n))).coeff 0) =
        ((G).sectionHom (e (MvPolynomial.X (s, n)))).coeff 0
      rw [(E).coeff_zero, (G).coeff_zero]
    · change e ((E).delta (MvPolynomial.X (s, n))) = (G).delta (e (MvPolynomial.X (s, n)))
      by_cases hs : s ∈ T
      · have h (k : ℕ) := relativeFreeSubsetSplitAlgEquiv_X_mem (A := A) T ⟨s, hs⟩ k
        simp only [relativeFreeDeltaStructure_delta_X, h]
      · have h (k : ℕ) := relativeFreeSubsetSplitAlgEquiv_X_compl (A := A) T ⟨s, hs⟩ k
        simp only [relativeFreeDeltaStructure_delta_X, h, relativeFreeDeltaStructure_delta_C]

/-- 同じ分離同型の逆方向もδ構造を保つ。 -/
theorem relativeFreeSubsetSplitAlgEquiv_symm_isDeltaHom :
    (G).IsDeltaHom E (e).symm.toRingHom := by
  intro x
  apply (e).injective
  change e ((e).symm ((G).delta x)) = e ((E).delta ((e).symm x))
  have h := relativeFreeSubsetSplitAlgEquiv_isDeltaHom T D ((e).symm x)
  change e ((E).delta ((e).symm x)) = (G).delta (e ((e).symm x)) at h
  rw [(e).apply_symm_apply] at h
  exact ((e).apply_symm_apply ((G).delta x)).trans h.symm

/-- 部分族内の元の反復δ関係は、補集合を係数にした同じ反復関係へ送られる。 -/
theorem relativeFreeSubsetSplitAlgEquiv_iteratedRelation (d : A) (a : σ → A)
    (s : T) (n : ℕ) :
    e (deltaDivisionIteratedRelation D d a (s : σ) n) =
      deltaDivisionIteratedRelation F (MvPolynomial.C d)
        (fun t : T => MvPolynomial.C (a t)) s n := by
  induction n with
  | zero =>
    change e (MvPolynomial.C d * MvPolynomial.X ((s : σ), 0) - MvPolynomial.C (a s)) = _
    simp [deltaDivisionIteratedRelation]
  | succ n ih =>
    have h := relativeFreeSubsetSplitAlgEquiv_isDeltaHom T D
      (deltaDivisionIteratedRelation D d a (s : σ) n)
    change e ((E).delta (deltaDivisionIteratedRelation D d a (s : σ) n)) =
      (G).delta (e (deltaDivisionIteratedRelation D d a (s : σ) n)) at h
    have h' := h.trans (congrArg (G).delta ih)
    simpa only [deltaDivisionIteratedRelation, Function.iterate_succ_apply'] using h'

/-- 部分根族の有限深さ関係イデアルは、係数拡大後の既存有限関係イデアルへ移る。 -/
theorem relativeFreeSubsetSplitAlgEquiv_map_finiteRelations
    (d : A) (a : σ → A) (N : ℕ) :
    (Ideal.span (Set.range fun z : T × Fin (N + 1) =>
      deltaDivisionIteratedRelation D d a (z.1 : σ) z.2.val)).map (e).toRingHom =
        deltaDivisionFiniteRelationIdeal F (MvPolynomial.C d)
          (fun t : T => MvPolynomial.C (a t)) N := by
  rw [Ideal.map_span, ← Set.range_comp']
  change Ideal.span (Set.range fun z : T × Fin (N + 1) =>
    e (deltaDivisionIteratedRelation D d a (z.1 : σ) z.2.val)) = _
  unfold deltaDivisionFiniteRelationIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext z
  exact relativeFreeSubsetSplitAlgEquiv_iteratedRelation T D d a z.1 z.2.val

omit [Fact p.Prime] in
/-- 元のmod(p,d)係数イデアルも、同じ分離同型の下で標準係数イデアルへ移る。 -/
theorem relativeFreeSubsetSplitAlgEquiv_map_pd (d : A) :
    (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d}).map
        (e).toRingHom =
      Ideal.span {(p : C), MvPolynomial.C (MvPolynomial.C d)} := by
  rw [Ideal.map_span]
  simp only [Set.image_pair, map_natCast]
  change Ideal.span {(p : C), e (MvPolynomial.C d)} = _
  rw [relativeFreeSubsetSplitAlgEquiv_C]

/-- 部分根族の実有限深さmod(p,d)商は、補集合を係数とする同じ有限関係商。 -/
def relativeFreeSubsetFiniteResidueQuotientEquiv (d : A) (a : σ → A) (N : ℕ) :
    (RelativeFreeDeltaRing (R := A) σ ⧸
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        Ideal.span (Set.range fun z : T × Fin (N + 1) =>
          deltaDivisionIteratedRelation D d a (z.1 : σ) z.2.val))) ≃+*
    (C ⧸ (Ideal.span {(p : C), MvPolynomial.C (MvPolynomial.C d)} ⊔
      deltaDivisionFiniteRelationIdeal F (MvPolynomial.C d)
        (fun t : T => MvPolynomial.C (a t)) N)) :=
  Ideal.quotientEquiv _ _ (e).toRingEquiv (by
    change _ = Ideal.map (e).toRingHom _
    rw [Ideal.map_sup, relativeFreeSubsetSplitAlgEquiv_map_pd,
      relativeFreeSubsetSplitAlgEquiv_map_finiteRelations])

end SerrePositivity.BhattScholze
