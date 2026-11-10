module

public import SerrePositivity.AlgebraicGeometry.StandardEtaleFractionModel
public import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
概要：多変数多項式環上の標準 étale 整域は、同じ分数体を持つモニックな超曲面模型を持つ。
方針：座標の最小多項式を、指定変数を追加した多変数多項式に移す。
規約：模型を定める商から分数体への埋め込みと、分数表示を与える。
使われ方：滑らかなアフィンの生成ファイバーの幾何学的整性を広げる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open MvPolynomial
open scoped Polynomial

/--
概要：体上の多変数多項式環の標準 étale 整域と、同じ分数体を持つ超曲面環が存在する。
方針：整閉な多変数多項式環上の最小多項式の商から、座標が生成する部分代数へ移す。
規約：超曲面方程式は追加変数についてモニック。
使われ方：共通分数体から、模型と元の代数の共通の主開を取る。
-/
theorem exists_monic_hypersurface_of_standardEtalePresentation
    {k σ B L : Type*} [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra (MvPolynomial σ k) B] [IsScalarTower k (MvPolynomial σ k) B]
    [Field L] [Algebra B L] [IsFractionRing B L] [Algebra k L]
    [Algebra (MvPolynomial σ k) L] [IsScalarTower k (MvPolynomial σ k) L]
    [IsScalarTower (MvPolynomial σ k) B L] [Module.IsTorsionFree (MvPolynomial σ k) L]
    (E : StandardEtalePresentation (MvPolynomial σ k) B) :
    ∃ (P : MvPolynomial (Option σ) k), (optionEquivLeft k σ P).Monic ∧
      ∃ (j : (MvPolynomial (Option σ) k ⧸ Ideal.span {P}) →ₐ[k] L),
        Function.Injective j ∧ ∀ z : L, ∃ x y, z = j x / j y := by
  let R := MvPolynomial σ k
  let : IsIntegrallyClosed R := UniqueFactorizationMonoid.instIsIntegrallyClosed
  let t := algebraMap B L E.x
  let m : R[X] := minpoly R t
  let e := optionEquivLeft k σ
  let P := e.symm m
  have hInt : IsIntegral R t :=
    (show IsIntegral R E.x from ⟨E.f, E.monic_f, E.hasMap.1⟩).map
      (IsScalarTower.toAlgHom R B L)
  have hMonic : (e P).Monic := by
    rw [e.apply_symm_apply]
    exact minpoly.monic hInt
  let I : Ideal (MvPolynomial (Option σ) k) := Ideal.span {P}
  let J : Ideal R[X] := Ideal.span {m}
  have hEq : J = I.map e.toRingHom := by
    change Ideal.span {m} = (Ideal.span {P}).map e.toRingHom
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {m} = Ideal.span {e P}
    rw [e.apply_symm_apply]
  let eQ := Ideal.quotientEquivAlg I J e hEq
  let v : R[X] →ₐ[R] L := Polynomial.aeval t
  let D := v.range
  let eR : AdjoinRoot m ≃ₐ[R] D :=
    adjoinRootMinpolyEquiv_aeval_range_of_standardEtalePresentation E
  let eD : (MvPolynomial (Option σ) k ⧸ I) ≃ₐ[k] D :=
    eQ.trans (eR.restrictScalars k)
  let j := (D.val.restrictScalars k).comp eD.toAlgHom
  refine ⟨P, hMonic, j, Subtype.val_injective.comp eD.injective, ?_⟩
  let : IsFractionRing D L := isFractionRing_aeval_range_of_standardEtalePresentation E
  intro z
  obtain ⟨x, y, _, h⟩ := IsFractionRing.div_surjective D z
  refine ⟨eD.symm x, eD.symm y, ?_⟩
  change z = (eD (eD.symm x)).1 / (eD (eD.symm y)).1
  rw [eD.apply_symm_apply, eD.apply_symm_apply]
  exact h.symm

end SerrePositivity.AlgebraicGeometry
