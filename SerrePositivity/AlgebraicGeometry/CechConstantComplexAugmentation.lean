module

public import SerrePositivity.AlgebraicGeometry.CechConstantAugmentation
public import SerrePositivity.AlgebraicGeometry.CechConstantComplex

/-!
概要：全縦次数に同じ基底項を持つ増大を、元の全タプル複体へ渡す。
方針：元の制限の合成則と、定数列の交代微分を各成分で照合する。
規約：零次singleからの包含と同じ増大を保ち、各成分の全射性は仮定しない。
使われ方：二重 Čech の行の完全性を元の増大された全複体へ渡す比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped BigOperators
universe u v
variable {R : Type v} [CommRing R] {ι : Type} [DecidableEq ι]
variable (D : Finset ι ⥤ ModuleCat.{u} R) (A : ModuleCat.{u} R) (α : A ⟶ D.obj ∅)

set_option backward.isDefEq.respectTransparency false in
/-- 全ての縦次数で、同じ基底の係数を元の有限像への制限で増大する。 -/
def fullCechConstantComplexAugmentation : cechConstantComplex A ⟶ fullCechComplex D where
  f n := α ≫ (fullCechConstantAugmentation D).app (SimplexCategory.mk n)
  comm' n m h := by
    have hm : n + 1 = m := h
    subst m
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext t
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, fullCechComplex,
      CochainComplex.of_d, ModuleCat.hom_ofHom]
    change fullCechDifferential D (n + 1)
        (fun s ↦ (D.map (homOfLE (Finset.empty_subset (cechTupleSupport s)))).hom (α.hom x)) t =
      (D.map (homOfLE (Finset.empty_subset (cechTupleSupport t)))).hom
        (α.hom (((cechConstantComplex A).d n (n + 1)).hom x))
    rw [fullCechDifferential_apply]
    have hc (i : Fin (n + 2)) :
        (D.map (homOfLE (cechTupleSupport_face_subset t i))).hom
          ((D.map (homOfLE (Finset.empty_subset
            (cechTupleSupport (t ∘ i.succAbove))))).hom (α.hom x)) =
        (D.map (homOfLE (Finset.empty_subset (cechTupleSupport t)))).hom (α.hom x) := by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← D.map_comp]
      rfl
    simp_rw [hc]
    rw [← Finset.sum_smul, Fin.sum_neg_one_pow, cechConstantComplex_d]
    split_ifs <;> simp only [zero_smul, one_smul, ModuleCat.hom_zero, ModuleCat.hom_id,
      LinearMap.zero_apply, LinearMap.id_apply, map_zero]
    all_goals rfl

/-- 同じ全次数の増大の評価は、元の空集合から有限像への制限。 -/
theorem fullCechConstantComplexAugmentation_apply (n : ℕ) (x : A)
    (t : Fin (n + 1) → ι) :
    ((fullCechConstantComplexAugmentation D A α).f n).hom x t =
      (D.map (homOfLE (Finset.empty_subset (cechTupleSupport t)))).hom (α.hom x) := rfl

/-- 元のsingleからの包含との合成の零次は、同じ元の増大。 -/
theorem fullCechConstantComplexAugmentation_single_zero :
    (cechConstantSingleAugmentation A ≫ fullCechConstantComplexAugmentation D A α).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℕ) 0 A).hom ≫
        α ≫ (fullCechConstantAugmentation D).app (SimplexCategory.mk 0) := by
  rw [HomologicalComplex.comp_f, cechConstantSingleAugmentation_f_zero]
  rfl

end SerrePositivity.AlgebraicGeometry
