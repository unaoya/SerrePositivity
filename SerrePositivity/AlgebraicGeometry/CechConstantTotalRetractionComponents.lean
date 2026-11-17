module

public import SerrePositivity.AlgebraicGeometry.CechConstantAugmentedDouble
public import SerrePositivity.HomologicalAlgebra.BicomplexProjection

/-!
概要：定数増大列から元のsingle増大列の全複体への補正付き射影の各次数を作る。
方針：正偶数縦次数の基底項を、負の増大で隣の水平成分へ送る。
規約：元の直和入射と増大を保持する。微分との可換性は次の分割で示す。
使われ方：同じ全複体で零次singleをretractとして取り出す比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u v
local notation "up" => ComplexShape.up ℕ
variable {R : Type v} [CommRing R] (A : ModuleCat.{u} R)
variable (F : CosimplicialObject (CochainComplex (ModuleCat.{u} R) ℕ))
variable (ε : (Functor.const SimplexCategory).obj (cechConstantComplex A) ⟶ F)
variable [hK : HomologicalComplex₂.HasTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up]
variable [hL : HomologicalComplex₂.HasTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up]
include A F ε hK hL

/-- 元の各直和項から、同じ補正付き成分の式でsingleのtotalへ送る。 -/
def cechConstantTotalRetractionSummand (a b n : ℕ)
    (h : ComplexShape.π up up up (a, b) = n) :
    ((SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)).X a).X b ⟶ (HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up).X n := by
  cases a with
  | succ a => exact HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up (a + 1) b n h
  | zero =>
    change A ⟶ (HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up).X n
    cases b with
    | zero =>
      have hn : n = 0 := h.symm
      subst n
      exact (HomologicalComplex.singleObjXSelf up 0 A).inv ≫ HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up 0 0 0 rfl
    | succ b =>
      by_cases hb : Even (b + 1)
      · exact -((ε.app (SimplexCategory.mk 0)).f b) ≫
          HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up 1 b n (by change 0 + (b + 1) = n at h; change 1 + b = n; omega)
      · exact 0

/-- 同じ各直和項の補正付きの式による、全複体の次数nの射。 -/
def cechConstantTotalRetractionComponent (n : ℕ) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up).X n ⟶ (HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up).X n :=
  HomologicalComplex₂.totalDesc (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) (fun a b h ↦ cechConstantTotalRetractionSummand A F ε a b n h)

/-- 正の水平列では、元の同じ直和入射を保持する。 -/
theorem cechConstantTotalRetractionComponent_ι_succ (a b n : ℕ)
    (h : ComplexShape.π up up up (a + 1, b) = n) :
    HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up (a + 1) b n h ≫ cechConstantTotalRetractionComponent A F ε n =
      HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up (a + 1) b n h := by
  rw [cechConstantTotalRetractionComponent, HomologicalComplex₂.ι_totalDesc (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε))]
  rfl

/-- 零次の基底項は、元のsingleの標準同型で送る。 -/
theorem cechConstantTotalRetractionComponent_ι_zero_zero :
    HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up 0 0 0 rfl ≫ cechConstantTotalRetractionComponent A F ε 0 =
      (HomologicalComplex.singleObjXSelf up 0 A).inv ≫ HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up 0 0 0 rfl := by
  rw [cechConstantTotalRetractionComponent, HomologicalComplex₂.ι_totalDesc (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε))]
  rfl

/-- 正の縦次数では、偶数の場合だけ負の元の増大で隣の水平成分へ補正する。 -/
theorem cechConstantTotalRetractionComponent_ι_zero_succ (b n : ℕ)
    (h : ComplexShape.π up up up (0, b + 1) = n) :
    HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up 0 (b + 1) n h ≫ cechConstantTotalRetractionComponent A F ε n =
      if hb : Even (b + 1) then
        -((ε.app (SimplexCategory.mk 0)).f b) ≫
          HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up 1 b n (by change 0 + (b + 1) = n at h; change 1 + b = n; omega)
      else 0 := by
  rw [cechConstantTotalRetractionComponent, HomologicalComplex₂.ι_totalDesc (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε))]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- 元の包含のtotalの各次数の射に、同じ補正付き成分を合成すると恒等。 -/
theorem cechConstantTotalRetractionComponent_section (n : ℕ) :
    (HomologicalComplex₂.total.map (cechSingleToConstantDouble A F ε) up).f n ≫
        cechConstantTotalRetractionComponent A F ε n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  cases a with
  | succ a =>
    rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc,
      cechSingleToConstantDouble_succ]
    change 𝟙 _ ≫ (HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up (a + 1) b n h ≫
        cechConstantTotalRetractionComponent A F ε n) = HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up (a + 1) b n h ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, cechConstantTotalRetractionComponent_ι_succ]
  | zero =>
    cases b with
    | zero =>
      have hn : n = 0 := h.symm
      subst n
      rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc,
        cechSingleToConstantDouble_zero]
      change (cechConstantSingleAugmentation A).f 0 ≫
          (HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up 0 0 0 rfl ≫ cechConstantTotalRetractionComponent A F ε 0) =
        HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up 0 0 0 rfl ≫ 𝟙 _
      rw [cechConstantSingleAugmentation_f_zero,
        cechConstantTotalRetractionComponent_ι_zero_zero]
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
    | succ b =>
      exact (HomologicalComplex.isZero_single_obj_X up 0 A (b + 1)
        (Nat.succ_ne_zero b)).eq_of_src _ _

end SerrePositivity.AlgebraicGeometry
