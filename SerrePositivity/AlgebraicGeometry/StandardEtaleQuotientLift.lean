module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Etale.StandardEtale

/-!
概要：商環上の標準 étale 代数を元の環へ持ち上げる。
方針：モニック多項式と局所化元を持ち上げ、微分も可逆にする。
規約：商写像は任意の全射な代数構造で表す。
使われ方：Stacks 057S で台の閉部分上の étale 近傍を周囲へ延ばす。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open Polynomial
open scoped TensorProduct

/--
概要：全射な基底写像の下で、標準 étale 代数を指定根とともに持ち上げられる。
方針：係数を持ち上げ、局所化元に微分を掛ける。商環側では微分が既に可逆なので、
商環側の代数との同型が得られる。
規約：元の環上の模型は標準 étale 対で表す。
使われ方：台の閉部分からの étale 近傍の持ち上げ。
-/
theorem exists_standardEtale_lift_of_surjective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (h : Function.Surjective (algebraMap R S)) (P : StandardEtalePair S) :
    ∃ (Q : StandardEtalePair R) (e : S ⊗[R] Q.Ring ≃ₐ[S] P.Ring),
      e (1 ⊗ₜ[R] Q.X) = P.X := by
  have hmf : P.f ∈ Polynomial.lifts (algebraMap R S) :=
    Polynomial.map_surjective _ h P.f
  obtain ⟨f, hf, _, hfm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hmf P.monic_f
  obtain ⟨g, hg⟩ := Polynomial.map_surjective _ h P.g
  let Q : StandardEtalePair R :=
    ⟨f, hfm, g * f.derivative, g, 0, 1, by simp [mul_comm]⟩
  let U := Q.map (algebraMap R S)
  have huf : U.f = P.f := hf
  have hug : U.g = P.g * P.f.derivative := by
    change (g * f.derivative).map (algebraMap R S) = _
    rw [Polynomial.map_mul, ← Polynomial.derivative_map, hg, hf]
  have hp : U.HasMap P.X := by
    refine ⟨huf.symm ▸ P.hasMap_X.1, ?_⟩
    rw [hug, map_mul]
    exact P.hasMap_X.2.mul P.hasMap_X.isUnit_derivative_f
  have hu : P.HasMap U.X := by
    refine ⟨huf ▸ U.hasMap_X.1, ?_⟩
    have hu' := U.hasMap_X.2
    rw [hug, map_mul] at hu'
    exact isUnit_of_dvd_unit (dvd_mul_right _ _) hu'
  let e : U.Ring ≃ₐ[S] P.Ring :=
    AlgEquiv.ofAlgHom (U.lift P.X hp) (P.lift U.X hu)
      (P.hom_ext (by simp)) (U.hom_ext (by simp))
  let p : StandardEtalePresentation R Q.Ring :=
    ⟨Q, Q.X, Q.hasMap_X, by rw [Q.lift_X_left]; exact Function.bijective_id⟩
  let d : S ⊗[R] Q.Ring ≃ₐ[S] U.Ring := (p.baseChange (T := S)).equivRing
  refine ⟨Q, d.trans e, ?_⟩
  have hd : d (1 ⊗ₜ[R] Q.X) = U.X := (p.baseChange (T := S)).equivRing_x
  change e (d (1 ⊗ₜ[R] Q.X)) = P.X
  rw [hd]
  exact U.lift_X P.X hp

end SerrePositivity.AlgebraicGeometry
