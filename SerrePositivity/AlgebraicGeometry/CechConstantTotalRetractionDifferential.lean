module

public import SerrePositivity.AlgebraicGeometry.CechConstantTotalRetractionComponents
import all SerrePositivity.HomologicalAlgebra.BicomplexProjection

/-!
概要：同じ補正付き射影の各成分を、元のtotalの微分と照合する。
方針：元の直和入射の微分の既存の式と、定数列の0/idの式を使う。
規約：正の水平成分と零次の基底成分を先に扱う。全次数の比較は続く分割で示す。
使われ方：元のsingleのtotalへの同じ補正付き射影を複体の射にする。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits Preadditive
universe u v
local notation "up" => ComplexShape.up ℕ
variable {R : Type v} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ各直和入射での全微分を、等しい実際の終域次数mで述べる。 -/
theorem cechBicomplex_total_d_summand_to
    (M : HomologicalComplex₂ (ModuleCat.{u} R) up up) [M.HasTotal up]
    (a b n m : ℕ) (h : ComplexShape.π up up up (a, b) = n) (hm : n + 1 = m) :
    M.ιTotal up a b n h ≫ (M.total up).d n m =
      (M.d a (a + 1)).f b ≫ M.ιTotal up (a + 1) b m
          (by change a + b = n at h; change (a + 1) + b = m; omega) +
        (-1 : ℤ) ^ a • ((M.X a).d b (b + 1) ≫ M.ιTotal up a (b + 1) m
          (by change a + b = n at h; change a + (b + 1) = m; omega)) := by
  cases hm
  exact SerrePositivity.HomologicalAlgebra.total_d_summand (C := ModuleCat.{u} R) M a b n h

variable (A : ModuleCat.{u} R)
variable (F : CosimplicialObject (CochainComplex (ModuleCat.{u} R) ℕ))
variable (ε : (Functor.const SimplexCategory).obj (cechConstantComplex A) ⟶ F)
variable [hK : HomologicalComplex₂.HasTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up]
variable [hL : HomologicalComplex₂.HasTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up]
include A F ε hK hL

set_option backward.isDefEq.respectTransparency false in
/-- 正の水平成分では、元の同じ二方向の微分を保持する。 -/
theorem cechConstantTotalRetractionComponent_comm_succ (a b n : ℕ)
    (h : ComplexShape.π up up up (a + 1, b) = n) :
    (HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up (a + 1) b n h ≫ cechConstantTotalRetractionComponent A F ε n) ≫
        (HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up).d n (n + 1) =
      (HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up (a + 1) b n h ≫ (HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up).d n (n + 1)) ≫
        cechConstantTotalRetractionComponent A F ε (n + 1) := by
  rw [cechConstantTotalRetractionComponent_ι_succ,
    SerrePositivity.HomologicalAlgebra.total_d_summand (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) (a + 1) b n h,
    SerrePositivity.HomologicalAlgebra.total_d_summand (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) (a + 1) b n h]
  simp only [add_comp, zsmul_comp, Category.assoc,
    cechConstantTotalRetractionComponent_ι_succ]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- 零次の基底成分では、元の同じsingleの標準同型と増大を保つ。 -/
theorem cechConstantTotalRetractionComponent_comm_zero :
    (HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up 0 0 0 rfl ≫ cechConstantTotalRetractionComponent A F ε 0) ≫
        (HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up).d 0 1 =
      (HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up 0 0 0 rfl ≫ (HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up).d 0 1) ≫
        cechConstantTotalRetractionComponent A F ε 1 := by
  let E : cechConstantComplex A ⟶ F.obj (SimplexCategory.mk 0) := ε.app (SimplexCategory.mk 0)
  rw [cechConstantTotalRetractionComponent_ι_zero_zero, Category.assoc,
    SerrePositivity.HomologicalAlgebra.total_d_summand (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) 0 0 0 rfl,
    SerrePositivity.HomologicalAlgebra.total_d_summand (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) 0 0 0 rfl]
  change (HomologicalComplex.singleObjXSelf up 0 A).inv ≫
      (((cechConstantSingleAugmentation A ≫ ε.app (SimplexCategory.mk 0)).f 0 ≫
          HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up 1 0 1 rfl) +
        (-1 : ℤ) ^ 0 • (((HomologicalComplex.single (ModuleCat.{u} R) up 0).obj A).d 0 1 ≫
          HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up 0 1 1 rfl)) =
    ((E.f 0 ≫ HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up 1 0 1 rfl) +
      (-1 : ℤ) ^ 0 • ((cechConstantComplex A).d 0 1 ≫ HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up 0 1 1 rfl)) ≫
      cechConstantTotalRetractionComponent A F ε 1
  rw [HomologicalComplex.comp_f, cechConstantSingleAugmentation_f_zero,
    HomologicalComplex.single_obj_d, cechConstantComplex_d,
    ite_eq_left (show Even 2 by decide)]
  simp only [pow_zero, one_smul, zero_comp, add_zero, Category.assoc,
    cechConstantTotalRetractionComponent_ι_succ, Iso.inv_hom_id_assoc]
  rfl

end SerrePositivity.AlgebraicGeometry
