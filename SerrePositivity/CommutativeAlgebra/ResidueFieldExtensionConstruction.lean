module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Field.Equiv

/-! # 剰余体拡大を作る単生成代数の基盤

任意の局所環上の整拡大について、閉ファイバーが体なら拡大環も局所環である。
モニック多項式の商の有限自由性と、係数を剰余体へ移した閉ファイバーの同型を
Mathlibから供給する。単生成拡大の後続段で使うので、Noether性・分離性を要求しない。
指定された体への同定、係数の持ち上げ、完備化は別の構成段階である。
-/

public section

namespace SerrePositivity

open IsLocalRing

/-- 整拡大の閉ファイバーが体なら、拡大環は局所環である。
各極大イデアルの収縮が基底の極大イデアルなので、閉ファイバーの極大イデアルが唯一となる。 -/
theorem isLocalRing_of_integral_of_field_closedFibre
    (B S : Type*) [CommRing B] [IsLocalRing B] [CommRing S] [Algebra B S]
    [Algebra.IsIntegral B S]
    (hfield : IsField (S ⧸ (maximalIdeal B).map (algebraMap B S))) : IsLocalRing S := by
  let J := (maximalIdeal B).map (algebraMap B S)
  have hJ : J.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient J).mpr hfield
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨J, hJ, fun P hP ↦ ?_⟩
  have hc : P.comap (algebraMap B S) = maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (algebraMap B S) (fun s ↦ Algebra.IsIntegral.isIntegral s) P)
  exact (hJ.eq_of_le hP.ne_top (Ideal.map_le_iff_le_comap.mpr hc.ge)).symm

/-- 閉ファイバーが体なら、拡大した極大イデアルは終域の極大イデアルに等しい。
終域の局所性を別途供給すれば、整性やNoether性はこの同定に不要。 -/
theorem maximalIdeal_map_eq_of_field_closedFibre
    (B S : Type*) [CommRing B] [IsLocalRing B] [CommRing S] [IsLocalRing S] [Algebra B S]
    (hfield : IsField (S ⧸ (maximalIdeal B).map (algebraMap B S))) :
    (maximalIdeal B).map (algebraMap B S) = maximalIdeal S :=
  IsLocalRing.eq_maximalIdeal
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hfield)

/-- モニック多項式を加えた代数は有限かつ平坦。有限自由性は既存の冪基底から得る。 -/
theorem adjoinRoot_finite_flat {B : Type*} [CommRing B] (F : Polynomial B) (hF : F.Monic) :
    Module.Finite B (AdjoinRoot F) ∧ Module.Flat B (AdjoinRoot F) := by
  let : Module.Free B (AdjoinRoot F) := hF.free_adjoinRoot
  exact ⟨hF.finite_adjoinRoot, inferInstance⟩

/-- 多項式を加えた代数の閉ファイバーは、剰余体上で同じ多項式を加えた代数である。
基底環上の代数同型として構成し、係数写像との両立を保持する。 -/
noncomputable def adjoinRoot_closedFibreEquiv
    {B : Type*} [CommRing B] [IsLocalRing B] (F : Polynomial B) :
    (AdjoinRoot F ⧸ (maximalIdeal B).map (algebraMap B (AdjoinRoot F))) ≃ₐ[B]
      AdjoinRoot (F.map (residue B)) :=
  AdjoinRoot.quotEquivQuotMap F (maximalIdeal B)

/-- 閉ファイバー同型は、持ち上げた根を還元多項式の根へ送る。 -/
@[simp] theorem adjoinRoot_closedFibreEquiv_root
    {B : Type*} [CommRing B] [IsLocalRing B] (F : Polynomial B) :
    adjoinRoot_closedFibreEquiv F (Ideal.Quotient.mk _ (AdjoinRoot.root F)) =
      AdjoinRoot.root (F.map (residue B)) := by
  have h := AdjoinRoot.quotEquivQuotMap_apply_mk F Polynomial.X (maximalIdeal B)
  rw [Polynomial.map_X] at h
  -- 剰余体と商、AdjoinRootと多項式商の定義上の同一視を、この適用だけで展開する。
  with_unfolding_all exact h

/-- 剰余体で既約になるモニック多項式の商は局所環である。
純非分離の既約多項式も含め、分離性は仮定しない。 -/
theorem adjoinRoot_isLocalRing_of_irreducible_reduction
    {B : Type*} [CommRing B] [IsLocalRing B] (F : Polynomial B) (hF : F.Monic)
    (hirr : Irreducible (F.map (residue B))) : IsLocalRing (AdjoinRoot F) := by
  let : Algebra.IsIntegral B (AdjoinRoot F) := AdjoinRoot.isIntegral_of_monic hF
  let : Fact (Irreducible (F.map (residue B))) := ⟨hirr⟩
  let : Field (AdjoinRoot (F.map (residue B))) := inferInstance
  apply isLocalRing_of_integral_of_field_closedFibre B (AdjoinRoot F)
  exact MulEquiv.isField (Field.toIsField _) (adjoinRoot_closedFibreEquiv F).toRingEquiv.toMulEquiv

end SerrePositivity
