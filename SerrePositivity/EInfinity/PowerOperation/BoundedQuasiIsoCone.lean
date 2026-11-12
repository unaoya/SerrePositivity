module

public import SerrePositivity.EInfinity.PowerOperation.BoundedAcyclicHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# 有界な係数の準同型の同じ cone

DAG XIII Construction 2.2.6 の周期解像度による係数比較に用いる補助。
一般のアーベル圏で、同じ準同型の cone の非輪状性と上有界性を供給する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- 指定準同型の同じ cone は非輪状。 -/
lemma coefficientCone_acyclic_of_quasiIso {M N : CochainComplex C ℤ} (f : M ⟶ N)
    [QuasiIso f] : (mappingCone f).Acyclic := by
  apply (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
  have hf : HomotopyCategory.quasiIso C (.up ℤ)
      ((HomotopyCategory.quotient C (.up ℤ)).map f) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mpr
      ((HomologicalComplex.mem_quasiIso_iff f).mpr inferInstance)
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hf
  exact ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).mp hf

/-- 同じ cone の非輪状性は、元の指定射の準同型性を反映する。 -/
lemma coefficientCone_quasiIso_of_acyclic {M N : CochainComplex C ℤ} (f : M ⟶ N)
    (h : (mappingCone f).Acyclic) : QuasiIso f := by
  have hc := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mpr h
  have hf := ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).mpr hc
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hf
  change HomotopyCategory.quasiIso C (.up ℤ)
    ((HomotopyCategory.quotient C (.up ℤ)).map f) at hf
  exact (HomologicalComplex.mem_quasiIso_iff f).mp
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).mp hf)

/-- 両入力の共通の上界は、その同じ cone の上界でもある。 -/
lemma coefficientCone_isStrictlyLE {M N : CochainComplex C ℤ} (f : M ⟶ N)
    (d : ℤ) [M.IsStrictlyLE d] [N.IsStrictlyLE d] : (mappingCone f).IsStrictlyLE d := by
  rw [isStrictlyLE_iff]
  intro i hi
  apply (mappingCone.isZero_X_iff f i).mpr
  exact ⟨M.isZero_of_isStrictlyLE d (i + 1) (by omega),
    N.isZero_of_isStrictlyLE d i hi⟩

end SerrePositivity.EInfinity.PowerOperation
