module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
概要：有限加群の任意の基底変更後の台は、元の零化イデアルを拡大した閉集合。
方針：素点での台への所属を剰余体とのテンソル積で判定し、体拡大の忠実平坦性を使う。
規約：相対 Noether 正規化で使う Stacks 057Q のアフィン加群の表示。
使われ方：ファイバーごとの加群の台を、一つの閉部分スキームのファイバーで表す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits TensorProduct
open scoped TensorProduct

universe u

/--
概要：有限加群を係数拡大した後の台は、元の台の逆像。
方針：二つの素点の剰余体を比較し、テンソル積の非自明性を体拡大で移す。
規約：係数拡大に平坦性を仮定しない。
使われ方：相対 Noether 正規化の前にファイバー上の台を計算する。
-/
theorem support_tensorProduct_eq_preimage
    (B C M : Type*) [CommRing B] [CommRing C] [Algebra B C]
    [AddCommGroup M] [Module B M] [Module.Finite B M] :
    Module.support C (C ⊗[B] M) =
      PrimeSpectrum.comap (algebraMap B C) ⁻¹' Module.support B M := by
  ext q
  let p := q.comap (algebraMap B C)
  let K := p.asIdeal.ResidueField
  let L := q.asIdeal.ResidueField
  change q ∈ Module.support C (C ⊗[B] M) ↔ p ∈ Module.support B M
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  let ι : K →ₐ[B] L := Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId B C) rfl
  let : Algebra K L := ι.toRingHom.toAlgebra
  let : IsScalarTower B K L := IsScalarTower.of_algebraMap_eq (fun b => (ι.commutes b).symm)
  change Nontrivial (L ⊗[C] (C ⊗[B] M)) ↔ Nontrivial (K ⊗[B] M)
  calc
    Nontrivial (L ⊗[C] (C ⊗[B] M)) ↔ Nontrivial (L ⊗[B] M) :=
      (AlgebraTensorModule.cancelBaseChange B C L L M).nontrivial_congr
    _ ↔ Nontrivial (L ⊗[K] (K ⊗[B] M)) :=
      (AlgebraTensorModule.cancelBaseChange B K L L M).nontrivial_congr.symm
    _ ↔ Nontrivial (K ⊗[B] M) := Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right K L

/--
概要：拡大した零化イデアルの零点集合は、係数拡大した有限加群の台。
方針：台の逆像の公式と、イデアルの拡大・縮小の随伴性を合わせる。
規約：零点集合は位相的な台を表す。
使われ方：剰余体への基底変更で、閉部分スキームのファイバーの点集合を同定する。
-/
theorem support_tensorProduct_eq_zeroLocus_map_annihilator
    (B C M : Type*) [CommRing B] [CommRing C] [Algebra B C]
    [AddCommGroup M] [Module B M] [Module.Finite B M] :
    Module.support C (C ⊗[B] M) =
      PrimeSpectrum.zeroLocus ((Module.annihilator B M).map (algebraMap B C) : Set C) := by
  rw [support_tensorProduct_eq_preimage, Module.support_eq_zeroLocus]
  ext q
  change (Module.annihilator B M : Set B) ⊆ (q.asIdeal.comap (algebraMap B C) : Set B) ↔ _
  rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, SetLike.coe_subset_coe,
    Ideal.map_le_iff_le_comap]

/--
概要：零化イデアルで定めた閉部分スキームの基底変更の像は、基底変更した有限加群の台。
方針：引き戻しの像を逆像として計算し、環論的な台の公式を使う。
規約：任意のアフィン基底変更を許すので、剰余体への基底変更にも適用できる。
使われ方：Stacks 057Q の台を表す閉部分スキームを、相対 Noether 正規化に渡す。
-/
theorem range_pullback_snd_quotientAnnihilator
    (B C : CommRingCat.{u}) [Algebra B C] (M : Type*) [AddCommGroup M] [Module B M]
    [Module.Finite B M] :
    Set.range (pullback.snd
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Module.annihilator B M))))
      (Spec.map (CommRingCat.ofHom (algebraMap B C)))) = Module.support C (C ⊗[B] M) := by
  rw [Scheme.Pullback.range_snd]
  change (PrimeSpectrum.comap (algebraMap B C)) ⁻¹'
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Module.annihilator B M))) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
    ← Module.support_eq_zeroLocus, support_tensorProduct_eq_preimage]

/--
概要：有限加群は零化イデアルで割った係数環上でも有限。
方針：元の有限生成性をスカラー制限から移す。
規約：商の加群構造は標準の零化イデアル商による。
使われ方：台を切り出した閉部分スキーム上へ加群を移す。
-/
theorem finite_quotientAnnihilator
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M] [Module.Finite B M] :
    letI := Module.quotientAnnihilator (R := B) (M := M)
    Module.Finite (B ⧸ Module.annihilator B M) M := by
  let := Module.quotientAnnihilator (R := B) (M := M)
  let : IsScalarTower B (B ⧸ Module.annihilator B M) M :=
    (Module.isTorsionBySet_annihilator B M).isScalarTower
  exact Module.Finite.of_restrictScalars_finite B _ _

end SerrePositivity.AlgebraicGeometry
