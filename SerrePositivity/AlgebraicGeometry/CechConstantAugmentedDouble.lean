module

public import SerrePositivity.AlgebraicGeometry.CechConstantComplex
public import SerrePositivity.HomologicalAlgebra.Cech.Basic

/-!
概要：同じ定数増大列と零次singleを、元の増大を保つ二重複体の射へまとめる。
方針：同じ包含と正の水平列の恒等を、B1の既存の増大複体関手へ渡す。
規約：元の全次数の増大を保持し、列ごとの射影や成分全射性は仮定しない。
使われ方：同じ全複体上の補正付き射影への入力。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type v} [CommRing R] (A : ModuleCat.{u} R)
variable (F : CosimplicialObject (CochainComplex (ModuleCat.{u} R) ℕ))
variable (ε : (Functor.const SimplexCategory).obj (cechConstantComplex A) ⟶ F)

/-- 全ての縦次数に同じAを持つ、元の増大射の図式。 -/
def cechConstantAugmentedObject :
    CosimplicialObject.Augmented (CochainComplex (ModuleCat.{u} R) ℕ) where
  left := cechConstantComplex A
  right := F
  hom := ε

/-- 元の零次singleからの包含を合成した、同じ増大の図式。 -/
def cechSingleAugmentedObject :
    CosimplicialObject.Augmented (CochainComplex (ModuleCat.{u} R) ℕ) where
  left := (HomologicalComplex.single (ModuleCat.{u} R) (.up ℕ) 0).obj A
  right := F
  hom :=
    { app n := cechConstantSingleAugmentation A ≫ ε.app n
      naturality {m n} a := by
        have he := ε.naturality a
        change 𝟙 _ ≫ ε.app n = ε.app m ≫ F.map a at he
        change 𝟙 _ ≫ (cechConstantSingleAugmentation A ≫ ε.app n) =
          (cechConstantSingleAugmentation A ≫ ε.app m) ≫ F.map a
        rw [Category.id_comp] at he ⊢
        rw [Category.assoc, ← he] }

/-- 同じ包含と正の水平列の恒等を持つ、元の増大図式の射。 -/
def cechSingleToConstantAugmented :
    cechSingleAugmentedObject A F ε ⟶ cechConstantAugmentedObject A F ε where
  left := cechConstantSingleAugmentation A
  right := 𝟙 F
  w := by
    apply NatTrans.ext
    funext n
    change cechConstantSingleAugmentation A ≫ ε.app n =
      (cechConstantSingleAugmentation A ≫ ε.app n) ≫ 𝟙 _
    exact (Category.comp_id _).symm

/-- 同じ包含をB1の既存の増大複体関手で写した二重複体の射。 -/
def cechSingleToConstantDouble :
    SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε) ⟶
      SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε) :=
  SerrePositivity.Cech.augmentedCochain.map (cechSingleToConstantAugmented A F ε)

/-- 零水平成分は、同じ零次singleから定数列への包含。 -/
theorem cechSingleToConstantDouble_zero :
    (cechSingleToConstantDouble A F ε).f 0 = cechConstantSingleAugmentation A := rfl

/-- 正の水平成分は、同じ元のFの恒等写像。 -/
theorem cechSingleToConstantDouble_succ (n : ℕ) :
    (cechSingleToConstantDouble A F ε).f (n + 1) = 𝟙 (F.obj (SimplexCategory.mk n)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- 同じ全次数の増大と縦微分の合成は、定数列の元の0/id微分に一致する。 -/
theorem cechConstantAugmentation_vertical (q : ℕ) :
    (ε.app (SimplexCategory.mk 0)).f q ≫
        (F.obj (SimplexCategory.mk 0)).d q (q + 1) =
      if Even (q + 2) then 0 else (ε.app (SimplexCategory.mk 0)).f (q + 1) := by
  have he := (ε.app (SimplexCategory.mk 0)).comm q (q + 1)
  change (ε.app (SimplexCategory.mk 0)).f q ≫ (F.obj (SimplexCategory.mk 0)).d q (q + 1) =
    (cechConstantComplex A).d q (q + 1) ≫ (ε.app (SimplexCategory.mk 0)).f (q + 1) at he
  have hd := congrArg (fun d : A ⟶ A ↦ d ≫ (ε.app (SimplexCategory.mk 0)).f (q + 1))
    (cechConstantComplex_d A q)
  exact he.trans (by split_ifs at hd ⊢ <;> simpa only [zero_comp, Category.id_comp] using hd)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ増大の後の水平微分は、既存B1の二回の微分の零性による。 -/
theorem cechConstantAugmentation_horizontal (q : ℕ) :
    (ε.app (SimplexCategory.mk 0)).f q ≫
        ((SerrePositivity.Cech.augmentedCochain.obj
          (cechConstantAugmentedObject A F ε)).d 1 2).f q = 0 := by
  let L := SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)
  change (L.d 0 1 ≫ L.d 1 2).f q = 0
  rw [L.d_comp_d]
  rfl

end SerrePositivity.AlgebraicGeometry
