module

public import SerrePositivity.CategoryTheory.Monoidal.AdjacentBraid
public import SerrePositivity.GroupTheory.Coxeter.TypeA
public import SerrePositivity.GroupTheory.Coxeter.InvolutionRelations
public import Mathlib.CategoryTheory.Endomorphism

/-!
# 反復テンソルへの対称群作用

型 A の提示から隣接交換を自己同型群へ延長し、対称群の同型と合成する。
一般の対称モノイダル圏の結果であり、球面や smash の定義には依存しない。
-/

@[expose] public section

universe v u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory SerrePositivity.Coxeter

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 隣接交換を反復テンソルの自己同型群の元として読む。 -/
noncomputable def adjacentAut (X : C) (n : ℕ) (i : Fin n) :
    Aut (power X (n + 1)) := Aut.of (adjacentIso X n i)

/-- 隣接交換の自己同型は対合。 -/
lemma adjacentAut_square (X : C) (n : ℕ) (i : Fin n) :
    adjacentAut X n i * adjacentAut X n i = 1 := by
  apply Aut.ext
  apply Iso.ext
  exact adjacentIso_involutive X n i

/-- 離れた位置の隣接交換は自己同型群でも可換。 -/
lemma adjacentAut_commute (X : C) (n : ℕ) (i j : Fin n) (h : i.val + 1 < j.val) :
    adjacentAut X n i * adjacentAut X n j = adjacentAut X n j * adjacentAut X n i := by
  apply Aut.ext
  apply Iso.ext
  exact (adjacentIso_commute X n i j h).symm

/-- 隣接した二つの交換は自己同型群でも braid 関係を満たす。 -/
lemma adjacentAut_braid (X : C) (n : ℕ) (i : Fin n) :
    adjacentAut X (n + 1) i.castSucc * adjacentAut X (n + 1) i.succ *
      adjacentAut X (n + 1) i.castSucc =
    adjacentAut X (n + 1) i.succ * adjacentAut X (n + 1) i.castSucc *
      adjacentAut X (n + 1) i.succ := by
  apply Aut.ext
  apply Iso.ext
  exact adjacentIso_braid X n i

/-- 隣接交換は型 A の Coxeter 関係を満たす。 -/
lemma adjacentAut_isLiftable (X : C) (n : ℕ) :
    CoxeterMatrix.IsLiftable (CoxeterMatrix.A n) (adjacentAut X n) := by
  intro i j
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  by_cases hij : i = j
  · subst j
    simp [adjacentAut_square]
  rw [ite_eq_right hij]
  by_cases hadj : j.val + 1 = i.val ∨ i.val + 1 = j.val
  · rw [ite_eq_left hadj]
    have hstep : ∀ (a b : Fin n), a.val + 1 = b.val →
        (adjacentAut X n a * adjacentAut X n b) ^ 3 = 1 := by
      intro a b h
      cases n with
      | zero => exact Fin.elim0 a
      | succ m =>
        have hlast : a ≠ Fin.last m := by
          intro hh
          subst a
          simp only [Fin.val_last] at h
          omega
        let k := a.castPred hlast
        have hk : k.castSucc = a := Fin.castSucc_castPred a hlast
        have hb : k.succ = b := by apply Fin.ext; simpa [k] using h
        have hbraid := adjacentAut_braid X m k
        rw [hk, hb] at hbraid
        exact involution_pair_cube _ _ (adjacentAut_square X _ a)
          (adjacentAut_square X _ b) hbraid
    rcases hadj with hji | hij'
    · have hrev := hstep j i hji
      have hi : (adjacentAut X n i)⁻¹ = adjacentAut X n i :=
        inv_eq_of_mul_eq_one_right (adjacentAut_square X n i)
      have hj : (adjacentAut X n j)⁻¹ = adjacentAut X n j :=
        inv_eq_of_mul_eq_one_right (adjacentAut_square X n j)
      have hc := congrArg (fun g ↦ g⁻¹) hrev
      simpa only [← inv_pow, mul_inv_rev, inv_one, hi, hj] using hc
    · exact hstep i j hij'
  · rw [ite_eq_right hadj]
    have hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val := by omega
    have hc : adjacentAut X n i * adjacentAut X n j =
        adjacentAut X n j * adjacentAut X n i := by
      rcases hfar with h | h
      · exact adjacentAut_commute X n i j h
      · exact (adjacentAut_commute X n j i h).symm
    exact involution_pair_square _ _ (adjacentAut_square X n i) (adjacentAut_square X n j) hc

/-- 正次数の反復テンソルに対する対称群の作用。 -/
noncomputable def positivePermutationAction (X : C) (n : ℕ) :
    Equiv.Perm (Fin (n + 1)) →* Aut (power X (n + 1)) :=
  ((CoxeterMatrix.A n).toCoxeterSystem.lift ⟨adjacentAut X n, adjacentAut_isLiftable X n⟩).comp
    (typeAEquivPerm n).symm.toMonoidHom

/-- 標準の隣接互換は構成済みの隣接交換へ送られる。 -/
lemma positivePermutationAction_adjacent (X : C) (n : ℕ) (i : Fin n) :
    positivePermutationAction X n (adjacentTransposition i) = adjacentAut X n i := by
  have hi : (typeAEquivPerm n).symm (adjacentTransposition i) =
      (CoxeterMatrix.A n).simple i := by
    rw [← typeAEquivPerm_simple n i]
    exact (typeAEquivPerm n).symm_apply_apply _
  change ((CoxeterMatrix.A n).toCoxeterSystem.lift
    ⟨adjacentAut X n, adjacentAut_isLiftable X n⟩)
      ((typeAEquivPerm n).symm (adjacentTransposition i)) = adjacentAut X n i
  rw [hi]
  exact CoxeterSystem.lift_apply_simple _ _ _

/-- 第0段も含む全次数の置換作用。第0段の置換は単位へ送る。 -/
noncomputable def permutationAction (X : C) :
    ∀ n, Equiv.Perm (Fin n) →* Aut (power X n)
  | 0 => 1
  | n + 1 => positivePermutationAction X n

/-- 全次数の作用における隣接互換の値。 -/
lemma permutationAction_adjacent (X : C) (n : ℕ) (i : Fin n) :
    permutationAction X (n + 1) (adjacentTransposition i) = adjacentAut X n i :=
  positivePermutationAction_adjacent X n i

/-- 恒等置換は恒等射へ送られる。 -/
lemma permutationAction_one (X : C) (n : ℕ) :
    (permutationAction X n 1).asIso.hom = 𝟙 (power X n) :=
  congrArg (fun a : Aut (power X n) ↦ a.asIso.hom) ((permutationAction X n).map_one)

/-- 置換の乗法は圏の合成と逆の順序で両立する。 -/
lemma permutationAction_mul (X : C) (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    (permutationAction X n (σ * τ)).asIso.hom =
      (permutationAction X n τ).asIso.hom ≫ (permutationAction X n σ).asIso.hom :=
  congrArg (fun a : Aut (power X n) ↦ a.asIso.hom) ((permutationAction X n).map_mul σ τ)

/-- 第0段では全ての置換が恒等射へ送られる。 -/
lemma permutationAction_zero (X : C) (σ : Equiv.Perm (Fin 0)) :
    (permutationAction X 0 σ).asIso.hom = 𝟙 (power X 0) := rfl

end SerrePositivity.TensorPowers
