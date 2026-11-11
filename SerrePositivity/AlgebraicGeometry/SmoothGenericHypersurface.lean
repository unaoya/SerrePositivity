module

public import SerrePositivity.AlgebraicGeometry.StandardEtaleHypersurface
public import SerrePositivity.AlgebraicGeometry.FractionFieldLocalizationComparison
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Smooth.Basic
import SerrePositivity.AlgebraicGeometry.HypersurfaceDomainEmbedding
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
概要：滑らかで幾何学的整なアフィン代数は、同じ分数体を持つ絶対既約な超曲面模型を持つ。
方針：生成点の標準 étale チャートで最小多項式を作り、体拡大後の埋め込みで絶対既約性を得る。
規約：超曲面方程式は追加した変数についてモニックとする。
使われ方：滑らかな生成ファイバーの幾何学的連結性を基底の稠密開に広げる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open MvPolynomial
open scoped TensorProduct nonZeroDivisors

/--
概要：体上の滑らかな幾何学的整域の分数体は、絶対既約なモニック超曲面環の分数体として表せる。
方針：標準 étale な主開を生成点に取り、その最小多項式の商を分数体に埋め込む。
規約：幾何学的整性は基底体の代数閉包へのテンソル積で表す。
使われ方：Stacks 0559 の滑らかな場合における生成ファイバーの超曲面模型。
-/
theorem exists_absoluteIrreducible_monic_hypersurface_of_smooth
    {k B : Type*} [Field k] [CommRing B] [IsDomain B] [Algebra k B] [Algebra.Smooth k B]
    [IsDomain (AlgebraicClosure k ⊗[k] B)] :
    ∃ (n : ℕ) (P : MvPolynomial (Option (Fin n)) k),
      (optionEquivLeft k (Fin n) P).Monic ∧
      Irreducible (map (algebraMap k (AlgebraicClosure k)) P) ∧
      ∃ (j : (MvPolynomial (Option (Fin n)) k ⧸ Ideal.span {P}) →ₐ[k] FractionRing B),
        Function.Injective j ∧ ∀ z : FractionRing B, ∃ x y, z = j x / j y := by
  obtain ⟨b, hb, n, alg, tower, het⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := (⊥ : Ideal B))
  have hb₀ : b ≠ 0 := fun h => hb (Ideal.mem_bot.mpr h)
  let C := Localization.Away b
  let R := MvPolynomial (Fin n) k
  let L := FractionRing B
  let : IsDomain C := Localization.Away.isDomain hb₀
  let : Algebra R C := alg
  let : IsScalarTower k R C := tower
  let : Algebra.IsStandardEtale R C := het
  let E : StandardEtalePresentation R C := Classical.choice inferInstance
  let u : C →+* L := IsLocalization.Away.lift b
    (IsLocalization.map_units L (⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb₀⟩ : B⁰))
  let : Algebra C L := u.toAlgebra
  let : IsScalarTower B C L := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq b _ x).symm
  let : IsFractionRing C L := IsFractionRing.isFractionRing_of_isLocalization
    (Submonoid.powers b) C L (powers_le_nonZeroDivisors_of_noZeroDivisors hb₀)
  let : Algebra R L := ((algebraMap C L).comp (algebraMap R C)).toAlgebra
  let : IsScalarTower R C L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k R L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply R C L, ← IsScalarTower.algebraMap_apply k R C,
      IsScalarTower.algebraMap_apply k B C, ← IsScalarTower.algebraMap_apply B C L,
      ← IsScalarTower.algebraMap_apply k B L]
  let : Module.IsTorsionFree R L := Module.isTorsionFree_iff_algebraMap_injective.mpr <| by
    rw [IsScalarTower.algebraMap_eq R C L]
    exact (IsFractionRing.injective C L).comp (FaithfulSMul.algebraMap_injective R C)
  obtain ⟨P, hP, j, hj, hFrac⟩ := exists_monic_hypersurface_of_standardEtalePresentation
    (k := k) (σ := Fin n) (L := L) E
  have hP₀ : P ≠ 0 := fun h => hP.ne_zero (by simp [h])
  let : IsDomain (AlgebraicClosure k ⊗[k] L) :=
    isDomain_tensor_fractionField_of_isDomain_tensor (B := B)
  exact ⟨n, P, hP, irreducible_map_of_hypersurface_injective P hP₀ j hj, j, hj, hFrac⟩

end SerrePositivity.AlgebraicGeometry
