module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PolynomialFrobeniusCech
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Cohomology
import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCohomology
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# 相対 Frobenius に沿う Čech の比較

## 概要
相対 Frobenius に沿う押し出しへの包含は、交代余面複体のホモトピー同値を誘導する。

## 方針
余り指数の基底で、全零添字の成分を分離する。他の添字では最初の非零頂点の
直前の零頂点を削り、係数には対応する余退化を施す。

## 規約
非正規化余鎖複体を使う。各指数は有限台なので、変数集合の有限性は不要。

## 使われ方
結晶比較の mod p の橋（BS 著者版 Lemma 5.4）。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial BigOperators

universe u

namespace SerrePositivity.BhattScholze.Prismatic

private def IsFirstNonzero {S : Type*} (z : S) {n : ℕ} (t : Fin n → S) (j : Fin n) : Prop :=
  t j ≠ z ∧ ∀ i, i < j → t i = z

private theorem IsFirstNonzero.unique {S : Type*} {z : S} {n : ℕ} {t : Fin n → S}
    {j j' : Fin n} (h : IsFirstNonzero z t j) (h' : IsFirstNonzero z t j') : j = j' :=
  le_antisymm (le_of_not_gt fun hj => h'.1 (h.2 j' hj))
    (le_of_not_gt fun hj => h.1 (h'.2 j hj))

private theorem IsFirstNonzero.insertNth {S : Type*} {z : S} {n : ℕ} {t : Fin n → S}
    {j : Fin n} (h : IsFirstNonzero z t j) (i : Fin (n + 1)) :
    IsFirstNonzero z (i.insertNth z t) (i.succAbove j) := by
  refine ⟨by simpa using h.1, ?_⟩
  intro k
  refine Fin.succAboveCases i (by simp) (fun l hl => ?_) k
  simp only [Fin.insertNth_apply_succAbove]
  exact h.2 l ((Fin.succAboveOrderEmb i).lt_iff_lt.mp hl)

private theorem firstNonzero_exists {S : Type*} {z : S} {n : ℕ} {t : Fin n → S}
    (ht : t ≠ fun _ => z) : ∃ j, IsFirstNonzero z t j := by
  classical
  have hn : ∃ i, t i ≠ z := by
    by_contra! h
    exact ht (funext h)
  let s := Finset.univ.filter (fun i => t i ≠ z)
  have hs : s.Nonempty := by simpa [s, Finset.Nonempty] using hn
  refine ⟨s.min' hs, (Finset.mem_filter.mp (Finset.min'_mem s hs)).2, fun i hi => ?_⟩
  by_contra h
  exact (not_le_of_gt hi) (Finset.min'_le s i (by simp [s, h]))

private theorem removeNth_insertNth_swap {S : Type*} {z : S} {n : ℕ} (t : Fin (n + 1) → S)
    (l : Fin (n + 1)) (i : Fin (n + 2)) :
    Fin.removeNth (α := fun _ => S) (i.succAbove l) (i.insertNth z t) =
      Fin.insertNth (α := fun _ => S) (l.predAbove i) z (l.removeNth t) := by
  symm
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · simp [Fin.removeNth, Fin.succAbove_succAbove_predAbove]
  · rw [← Fin.removeNth_removeNth_eq_swap, Fin.removeNth_insertNth]

private theorem insertNth_const {S : Type*} (z : S) {n : ℕ} (i : Fin (n + 1)) :
    i.insertNth z (fun _ => z) = fun _ => z := by
  funext j
  exact Fin.succAboveCases i (by simp) (fun k => by simp) j

section Pointed

variable {S : Type*} (z : S) (N : CosimplicialObject AddCommGrpCat.{u})

private abbrev Coeff (n : ℕ) := N.obj ⦋n⦌
private abbrev Term (n : ℕ) := (Fin (n + 1) → S) →₀ Coeff N n

private def face {n : ℕ} (i : Fin (n + 2)) : Term (S := S) N n →+ Term (S := S) N (n + 1) :=
  Finsupp.liftAddHom fun t =>
    (Finsupp.singleAddHom (i.insertNth z t)).comp (N.map (SimplexCategory.δ i)).hom

private theorem face_single {n : ℕ} (i : Fin (n + 2)) (t : Fin (n + 1) → S) (a : Coeff N n) :
    face z N i (Finsupp.single t a) =
      Finsupp.single (i.insertNth z t) (N.map (SimplexCategory.δ i) a) := by
  simp [face]

private def alt (n : ℕ) : Term (S := S) N n →+ Term (S := S) N (n + 1) :=
  ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • face z N i

private def proj (n : ℕ) : Term (S := S) N n →+ Coeff N n :=
  Finsupp.applyAddHom (fun _ => z)

private def incl (n : ℕ) : Coeff N n →+ Term (S := S) N n :=
  Finsupp.singleAddHom (fun _ => z)

private def lower (n : ℕ) (t : Fin (n + 2) → S) (j : Fin (n + 1)) :
    Coeff N (n + 1) →+ Term (S := S) N n :=
  ((-1 : ℤ) ^ j.val) •
    (Finsupp.singleAddHom (j.castSucc.removeNth t)).comp (N.map (SimplexCategory.σ j)).hom

private def lowerChoice (n : ℕ) (t : Fin (n + 2) → S) :
    Coeff N (n + 1) →+ Term (S := S) N n := by
  classical
  exact if h : ∃ j : Fin (n + 1), IsFirstNonzero z t j.succ then
    lower N n t h.choose
  else 0

private def contract (n : ℕ) : Term (S := S) N (n + 1) →+ Term (S := S) N n :=
  Finsupp.liftAddHom (lowerChoice z N n)

private theorem contract_single_zero (n : ℕ) (a : Coeff N (n + 1)) :
    contract z N n (Finsupp.single (fun _ => z) a) = 0 := by
  classical
  simp [contract, lowerChoice, IsFirstNonzero]

private theorem contract_single_first_zero (n : ℕ) (t : Fin (n + 2) → S)
    (h : IsFirstNonzero z t 0) (a : Coeff N (n + 1)) :
    contract z N n (Finsupp.single t a) = 0 := by
  classical
  have hh : ¬ ∃ j : Fin (n + 1), IsFirstNonzero z t j.succ := by
    rintro ⟨j, hj⟩
    exact Fin.succ_ne_zero j (hj.unique h)
  simp [contract, lowerChoice, hh]

private theorem contract_single_first_succ (n : ℕ) (t : Fin (n + 2) → S)
    (j : Fin (n + 1)) (h : IsFirstNonzero z t j.succ) (a : Coeff N (n + 1)) :
    contract z N n (Finsupp.single t a) =
      ((-1 : ℤ) ^ j.val) • Finsupp.single (j.castSucc.removeNth t)
        (N.map (SimplexCategory.σ j) a) := by
  classical
  let hex : ∃ i : Fin (n + 1), IsFirstNonzero z t i.succ := ⟨j, h⟩
  rw [contract, Finsupp.liftAddHom_apply_single, lowerChoice, dite_eq_left hex]
  have hj : hex.choose = j :=
    Fin.succ_injective _ (IsFirstNonzero.unique hex.choose_spec h)
  rw [hj]
  rfl

private theorem central {n : ℕ} (t : Fin (n + 1) → S) (j : Fin (n + 1))
    (ht : IsFirstNonzero z t j) (a : Coeff N n) :
    ((-1 : ℤ) ^ j.castSucc.val) •
      contract z N n (face z N j.castSucc (Finsupp.single t a)) = Finsupp.single t a := by
  rw [face_single]
  have h := ht.insertNth j.castSucc
  rw [Fin.succAbove_castSucc_self] at h
  rw [contract_single_first_succ z N n _ j h, Fin.removeNth_insertNth]
  have hδ : N.map (SimplexCategory.σ j) (N.map (SimplexCategory.δ j.castSucc) a) = a := by
    change (N.map (SimplexCategory.δ j.castSucc) ≫ N.map (SimplexCategory.σ j)) a = a
    rw [← N.map_comp, SimplexCategory.δ_comp_σ_self, N.map_id]
    rfl
  rw [hδ, smul_smul, Fin.val_castSucc, ← mul_pow]
  simp

private theorem offCenter_zero {n : ℕ} (t : Fin (n + 1) → S)
    (ht : IsFirstNonzero z t 0) (a : Coeff N n) (i : Fin (n + 1)) :
    contract z N n (face z N i.succ (Finsupp.single t a)) = 0 := by
  rw [face_single]
  have h := ht.insertNth i.succ
  rw [Fin.succAbove_of_castSucc_lt _ _ (by simp)] at h
  exact contract_single_first_zero z N n _ h _

private theorem paired (n : ℕ) (t : Fin (n + 2) → S) (j : Fin (n + 1))
    (ht : IsFirstNonzero z t j.succ) (a : Coeff N (n + 1)) (i : Fin (n + 2)) :
    ((-1 : ℤ) ^ (j.succ.castSucc.succAbove i).val) •
      contract z N (n + 1) (face z N (j.succ.castSucc.succAbove i) (Finsupp.single t a)) =
    - (((-1 : ℤ) ^ i.val) • face z N i (contract z N n (Finsupp.single t a))) := by
  rw [face_single, contract_single_first_succ z N n t j ht, map_zsmul, face_single]
  by_cases hi : i ≤ j.castSucc
  · have hij : i < j.succ := Fin.le_castSucc_iff.mp hi
    rw [Fin.succAbove_castSucc_of_lt _ _ hij]
    have h := ht.insertNth i.castSucc
    rw [Fin.succAbove_castSucc_of_le _ _ hij.le] at h
    rw [contract_single_first_succ z N (n + 1) _ j.succ h]
    have htuple : Fin.removeNth (α := fun _ => S) j.succ.castSucc (i.castSucc.insertNth z t) =
        i.insertNth z (j.castSucc.removeNth t) := by
      have hh := removeNth_insertNth_swap (z := z) t j.castSucc i.castSucc
      rwa [Fin.predAbove_castSucc_of_le _ _ hi,
        Fin.succAbove_castSucc_of_le _ _ hi, Fin.succ_castSucc] at hh
    have hδ : N.map (SimplexCategory.σ j.succ) (N.map (SimplexCategory.δ i.castSucc) a) =
        N.map (SimplexCategory.δ i) (N.map (SimplexCategory.σ j) a) := by
      change (N.map (SimplexCategory.δ i.castSucc) ≫ N.map (SimplexCategory.σ j.succ)) a =
        (N.map (SimplexCategory.σ j) ≫ N.map (SimplexCategory.δ i)) a
      rw [← N.map_comp, ← N.map_comp, SimplexCategory.δ_comp_σ_of_le hi]
    rw [htuple, hδ, Fin.val_castSucc, Fin.val_succ, pow_succ]
    simp
  · have hij : j.succ ≤ i := Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hi)
    have hji : j.castSucc ≤ i := (Fin.castSucc_lt_succ (i := j)).le.trans hij
    rw [Fin.succAbove_castSucc_of_le _ _ hij]
    have h := ht.insertNth i.succ
    rw [Fin.succAbove_succ_of_le _ _ hij, ← Fin.succ_castSucc] at h
    rw [contract_single_first_succ z N (n + 1) _ j.castSucc h]
    have htuple : Fin.removeNth (α := fun _ => S) j.castSucc.castSucc (i.succ.insertNth z t) =
        i.insertNth z (j.castSucc.removeNth t) := by
      have hh := removeNth_insertNth_swap (z := z) t j.castSucc i.succ
      rwa [Fin.predAbove_succ_of_le _ _ hji, Fin.succAbove_succ_of_le _ _ hji] at hh
    have hδ : N.map (SimplexCategory.σ j.castSucc) (N.map (SimplexCategory.δ i.succ) a) =
        N.map (SimplexCategory.δ i) (N.map (SimplexCategory.σ j) a) := by
      change (N.map (SimplexCategory.δ i.succ) ≫ N.map (SimplexCategory.σ j.castSucc)) a =
        (N.map (SimplexCategory.σ j) ≫ N.map (SimplexCategory.δ i)) a
      rw [← N.map_comp, ← N.map_comp, SimplexCategory.δ_comp_σ_of_gt (lt_of_not_ge hi)]
    rw [htuple, hδ, Fin.val_castSucc, Fin.val_succ, pow_succ]
    simp

private theorem contract_alt_zero {n : ℕ} (a : Coeff N n) :
    contract z N n (alt z N n (Finsupp.single (fun _ => z) a)) = 0 := by
  simp only [alt, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply, map_sum, map_zsmul,
    face_single, insertNth_const, contract_single_zero, smul_zero, Finset.sum_const_zero]

private theorem contract_alt_first_zero {n : ℕ} (t : Fin (n + 1) → S)
    (ht : IsFirstNonzero z t 0) (a : Coeff N n) :
    contract z N n (alt z N n (Finsupp.single t a)) = Finsupp.single t a := by
  simp only [alt, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply, map_sum, map_zsmul]
  rw [Fin.sum_univ_succ]
  simp only [offCenter_zero z N t ht a, smul_zero, Finset.sum_const_zero, add_zero]
  exact central z N t 0 ht a

private theorem contract_alt_first_succ (n : ℕ) (t : Fin (n + 2) → S)
    (j : Fin (n + 1)) (ht : IsFirstNonzero z t j.succ) (a : Coeff N (n + 1)) :
    contract z N (n + 1) (alt z N (n + 1) (Finsupp.single t a)) =
      Finsupp.single t a - alt z N n (contract z N n (Finsupp.single t a)) := by
  simp only [alt, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply, map_sum, map_zsmul]
  rw [Fin.sum_univ_succAbove _ j.succ.castSucc, central z N t j.succ ht a]
  simp only [paired z N n t j ht a, Finset.sum_neg_distrib, sub_eq_add_neg]

private theorem proj_single_eq {n : ℕ} (a : Coeff N n) :
    proj z N n (Finsupp.single (fun _ => z) a) = a := by
  classical
  simp [proj]

private theorem proj_single_ne {n : ℕ} (t : Fin (n + 1) → S) (a : Coeff N n)
    (ht : t ≠ fun _ => z) : proj z N n (Finsupp.single t a) = 0 := by
  classical
  simp [proj, ht]

private theorem incl_proj (n : ℕ) (a : Coeff N n) : proj z N n (incl z N n a) = a :=
  proj_single_eq z N a

private theorem contraction_zero :
    AddMonoidHom.id (Term (S := S) N 0) =
      (contract z N 0).comp (alt z N 0) + (incl z N 0).comp (proj z N 0) := by
  apply Finsupp.addHom_ext
  intro t a
  change Finsupp.single t a = contract z N 0 (alt z N 0 (Finsupp.single t a)) +
    incl z N 0 (proj z N 0 (Finsupp.single t a))
  by_cases ht : t = fun _ => z
  · subst t
    simp only [contract_alt_zero, proj_single_eq, zero_add]
    rfl
  · obtain ⟨j, hj⟩ := firstNonzero_exists ht
    have hj0 : j = 0 := Fin.eq_zero j
    subst j
    rw [contract_alt_first_zero z N t hj, proj_single_ne z N t a ht, map_zero, add_zero]

private theorem contraction_succ (n : ℕ) :
    AddMonoidHom.id (Term (S := S) N (n + 1)) =
      (contract z N (n + 1)).comp (alt z N (n + 1)) +
      (alt z N n).comp (contract z N n) + (incl z N (n + 1)).comp (proj z N (n + 1)) := by
  apply Finsupp.addHom_ext
  intro t a
  change Finsupp.single t a =
    contract z N (n + 1) (alt z N (n + 1) (Finsupp.single t a)) +
    alt z N n (contract z N n (Finsupp.single t a)) +
    incl z N (n + 1) (proj z N (n + 1) (Finsupp.single t a))
  by_cases ht : t = fun _ => z
  · subst t
    rw [contract_alt_zero, contract_single_zero, proj_single_eq, map_zero, zero_add, zero_add]
    rfl
  · rw [proj_single_ne z N t a ht, map_zero, add_zero]
    obtain ⟨j, hj⟩ := firstNonzero_exists ht
    revert hj
    refine Fin.cases (fun hj => ?_) (fun j hj => ?_) j
    · rw [contract_alt_first_zero z N t hj, contract_single_first_zero z N n t hj,
        map_zero, add_zero]
    · rw [contract_alt_first_succ z N n t j hj, sub_add_cancel]

private theorem proj_coface {n : ℕ} (i : Fin (n + 2)) :
    (proj z N (n + 1)).comp (face z N i) =
      (N.map (SimplexCategory.δ i)).hom.comp (proj z N n) := by
  apply Finsupp.addHom_ext
  intro t a
  change proj z N (n + 1) (face z N i (Finsupp.single t a)) =
    N.map (SimplexCategory.δ i) (proj z N n (Finsupp.single t a))
  rw [face_single]
  by_cases ht : t = fun _ => z
  · subst t
    rw [insertNth_const, proj_single_eq, proj_single_eq]
  · have h : i.insertNth z t ≠ fun _ => z := by
      intro he
      apply ht
      funext j
      simpa using congrFun he (i.succAbove j)
    rw [proj_single_ne z N _ _ h, proj_single_ne z N t a ht, map_zero]

end Pointed

section Frobenius

open SerrePositivity.Cosimplicial

variable (p : ℕ) {k : Type u} [CommRing k] {σ : Type}
    (N : CosimplicialObject CommRingCat.{u}) (ι : polynomialCech k σ ⟶ N) (hp : 0 < p)

local notation "U" => (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)

private abbrev pushoutFrob := pushout ι (relativeFrobeniusCech p k σ)

private abbrev K (X : CosimplicialObject CommRingCat.{u}) :=
  (alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (X ⋙ U)

private def reprFrob (n : ℕ) :
    (K (pushoutFrob p N ι)).X n ≃+
      Term (S := PolynomialExponentRemainder p σ) (N ⋙ U) n :=
  frobeniusPushoutRepr p ι hp ⦋n⦌

private abbrev zeroRemainder : PolynomialExponentRemainder p σ :=
  ⟨0, fun _ => hp⟩

private theorem reprFrob_coface {n : ℕ} (i : Fin (n + 2))
    (x : (pushoutFrob p N ι).obj ⦋n⦌) :
    reprFrob p N ι hp (n + 1) ((pushoutFrob p N ι).map (SimplexCategory.δ i) x) =
      face (zeroRemainder (σ := σ) p hp) (N ⋙ U) i (reprFrob p N ι hp n x) := by
  let e := frobeniusPushoutRepr p ι hp ⦋n⦌
  let e' := frobeniusPushoutRepr p ι hp ⦋n + 1⦌
  let m := ((pushoutFrob p N ι).map (SimplexCategory.δ i)).hom.toAddMonoidHom
  have he : e'.toAddMonoidHom.comp (m.comp e.symm.toAddMonoidHom) =
      face (zeroRemainder (σ := σ) p hp) (N ⋙ U) i := by
    apply Finsupp.addHom_ext
    intro t a
    rw [face_single]
    exact frobeniusPushoutRepr_coface_single p ι hp n i a t
  have h := DFunLike.congr_fun he (e x)
  change e' (m (e.symm (e x))) = _ at h
  rwa [e.symm_apply_apply] at h

private theorem K_d_apply (X : CosimplicialObject CommRingCat.{u}) (n : ℕ)
    (x : (K X).X n) :
    (K X).d n (n + 1) x =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • X.map (SimplexCategory.δ i) x :=
  (ringCochainComplex_d_apply X n x).trans (cochainDifferential_apply X n x)

private theorem reprFrob_d (n : ℕ) (x : (K (pushoutFrob p N ι)).X n) :
    reprFrob p N ι hp (n + 1) ((K (pushoutFrob p N ι)).d n (n + 1) x) =
      alt (zeroRemainder (σ := σ) p hp) (N ⋙ U) n (reprFrob p N ι hp n x) := by
  rw [K_d_apply]
  change reprFrob p N ι hp (n + 1) (∑ i : Fin (n + 2),
    (-1 : ℤ) ^ i.val • (show (K (pushoutFrob p N ι)).X (n + 1) from
      (pushoutFrob p N ι).map (SimplexCategory.δ i) x)) = _
  simp only [map_sum, alt, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  let e := reprFrob p N ι hp (n + 1)
  let a : (K (pushoutFrob p N ι)).X (n + 1) :=
    (pushoutFrob p N ι).map (SimplexCategory.δ i) x
  let c := (-1 : ℤ) ^ i.val
  exact (map_zsmul e c a).trans (congrArg (c • ·) (reprFrob_coface p N ι hp i x))

private def retractFrob (n : ℕ) : (K (pushoutFrob p N ι)).X n ⟶ (K N).X n :=
  AddCommGrpCat.ofHom <|
    (proj (zeroRemainder (σ := σ) p hp) (N ⋙ U) n).comp (reprFrob p N ι hp n).toAddMonoidHom

private def retractCochain : K (pushoutFrob p N ι) ⟶ K N :=
  CochainComplex.ofHom (retractFrob p N ι hp) fun n => by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    let z := zeroRemainder (σ := σ) p hp
    change (K N).d n (n + 1)
        (proj z (N ⋙ U) n (reprFrob p N ι hp n x)) =
      proj z (N ⋙ U) (n + 1) (reprFrob p N ι hp (n + 1)
        ((K (pushoutFrob p N ι)).d n (n + 1) x))
    rw [reprFrob_d p N ι hp]
    erw [K_d_apply N n (proj z (N ⋙ U) n (reprFrob p N ι hp n x))]
    simp only [alt, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact (DFunLike.congr_fun (proj_coface z (N ⋙ U) i) (reprFrob p N ι hp n x)).symm

private abbrev includeCochain : K N ⟶ K (pushoutFrob p N ι) :=
  (alternatingCofaceMapComplex _).map
    (Functor.whiskerRight (pushout.inl ι (relativeFrobeniusCech p k σ)) U)

private theorem reprFrob_include (n : ℕ) (x : (K N).X n) :
    reprFrob p N ι hp n ((includeCochain p N ι).f n x) =
      incl (zeroRemainder (σ := σ) p hp) (N ⋙ U) n x :=
  frobeniusPushoutRepr_inl p ι hp ⦋n⦌ x

private theorem include_retract :
    includeCochain p N ι ≫ retractCochain p N ι hp = 𝟙 _ := by
  ext n : 1
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change proj (zeroRemainder (σ := σ) p hp) (N ⋙ U) n
    (reprFrob p N ι hp n ((includeCochain p N ι).f n x)) = x
  rw [reprFrob_include]
  exact incl_proj (zeroRemainder (σ := σ) p hp) (N ⋙ U) n x

private def contractFrob (n : ℕ) :
    (K (pushoutFrob p N ι)).X (n + 1) ⟶ (K (pushoutFrob p N ι)).X n :=
  AddCommGrpCat.ofHom <| (reprFrob p N ι hp n).symm.toAddMonoidHom.comp <|
    (contract (zeroRemainder (σ := σ) p hp) (N ⋙ U) n).comp
      (reprFrob p N ι hp (n + 1)).toAddMonoidHom

private theorem reprFrob_contract (n : ℕ) (x : (K (pushoutFrob p N ι)).X (n + 1)) :
    reprFrob p N ι hp n (contractFrob p N ι hp n x) =
      contract (zeroRemainder (σ := σ) p hp) (N ⋙ U) n (reprFrob p N ι hp (n + 1) x) :=
  AddEquiv.apply_symm_apply _ _

private def homFrob (i j : ℕ) :
    (K (pushoutFrob p N ι)).X i ⟶ (K (pushoutFrob p N ι)).X j :=
  if h : i = j + 1 then h.symm ▸ contractFrob p N ι hp j else 0

private theorem homFrob_succ (j : ℕ) : homFrob p N ι hp (j + 1) j =
    contractFrob p N ι hp j := by simp [homFrob]

private def homotopyFrob :
    Homotopy (𝟙 (K (pushoutFrob p N ι)))
      (retractCochain p N ι hp ≫ includeCochain p N ι) where
  hom := homFrob p N ι hp
  zero i j h := by
    have h' : i ≠ j + 1 := fun w => h w.symm
    simp [homFrob, h']
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel i (i + 1) from rfl), homFrob_succ]
    cases i with
    | zero =>
      rw [prevD_eq_zero _ _ (by simp [ComplexShape.up_Rel])]
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      apply (reprFrob p N ι hp 0).injective
      change reprFrob p N ι hp 0 x =
        reprFrob p N ι hp 0 (contractFrob p N ι hp 0 ((K (pushoutFrob p N ι)).d 0 1 x) +
          0 + (includeCochain p N ι).f 0 (retractFrob p N ι hp 0 x))
      rw [add_zero, map_add, reprFrob_contract, reprFrob_d, reprFrob_include]
      exact DFunLike.congr_fun (contraction_zero (zeroRemainder (σ := σ) p hp) (N ⋙ U)) _
    | succ n =>
      rw [prevD_eq _ (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl), homFrob_succ]
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      apply (reprFrob p N ι hp (n + 1)).injective
      change reprFrob p N ι hp (n + 1) x =
        reprFrob p N ι hp (n + 1)
          (contractFrob p N ι hp (n + 1) ((K (pushoutFrob p N ι)).d (n + 1) (n + 2) x) +
            (K (pushoutFrob p N ι)).d n (n + 1) (contractFrob p N ι hp n x) +
            (includeCochain p N ι).f (n + 1) (retractFrob p N ι hp (n + 1) x))
      simp only [map_add, reprFrob_contract, reprFrob_d, reprFrob_include]
      exact DFunLike.congr_fun (contraction_succ (zeroRemainder (σ := σ) p hp) (N ⋙ U) n) _

private def frobeniusCechEquiv : HomotopyEquiv (K N) (K (pushoutFrob p N ι)) where
  hom := includeCochain p N ι
  inv := retractCochain p N ι hp
  homotopyHomInvId := Homotopy.ofEq (include_retract p N ι hp)
  homotopyInvHomId := (homotopyFrob p N ι hp).symm

end Frobenius

/-- 概要：相対 Frobenius に沿う押し出しへの包含はコホモロジー同型。
（BS 著者版 Lemma 5.4 の、N が余単体的可換環の場合）
方針：有限台指数の余りで各項を分解し、全零添字の成分以外を余鎖収縮する。
規約：変数集合は任意。非正規化の交代余面複体を使う。
使われ方：結晶比較の mod p の橋。 -/
theorem frobeniusTwist_cech_quasiIso_infinite (p : ℕ) [Fact p.Prime]
    (k : Type u) [CommRing k] (_hk : (p : k) = 0) (σ : Type)
    (N : CosimplicialObject CommRingCat.{u}) (ι : polynomialCech k σ ⟶ N) :
    SerrePositivity.Cosimplicial.IsCohomologyIso (pushout.inl ι (relativeFrobeniusCech p k σ)) := by
  intro n
  let e := frobeniusCechEquiv p N ι (Fact.out : Nat.Prime p).pos
  exact ConcreteCategory.bijective_of_isIso (e.toHomologyIso n).hom

/-- 概要：有限変数の場合の相対 Frobenius に沿う Čech 比較。
（BS 著者版 Lemma 5.4 の、N が余単体的可換環の場合）
方針：任意の変数集合についての余鎖収縮を用いる。
規約：有限変数版の引数を保つ。
使われ方：有限変数の多項式代数の結晶比較。 -/
theorem frobeniusTwist_cech_quasiIso (p : ℕ) [Fact p.Prime]
    (k : Type u) [CommRing k] (hk : (p : k) = 0) (σ : Type) [Finite σ]
    (N : CosimplicialObject CommRingCat.{u}) (ι : polynomialCech k σ ⟶ N) :
    SerrePositivity.Cosimplicial.IsCohomologyIso (pushout.inl ι (relativeFrobeniusCech p k σ)) :=
  frobeniusTwist_cech_quasiIso_infinite p k hk σ N ι

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Lemma 5.4" (partial := special) "N が余単体的可換環の場合（変数は任意、設計の決定どおり）。一般の B^{•,(1)} 加群 N は作らない ／ 11-10 更新"] _root_.SerrePositivity.BhattScholze.Prismatic.frobeniusTwist_cech_quasiIso
attribute [cite BS19 "Lemma 5.4" (partial := special) "N が余単体的可換環の場合（変数は任意、設計の決定どおり）。一般の B^{•,(1)} 加群 N は作らない ／ 11-10 更新"] _root_.SerrePositivity.BhattScholze.Prismatic.frobeniusTwist_cech_quasiIso_infinite
