module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorFreeRight
public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorSymmetry

/-! # 自由加群を左因子とする釣り合いテンソル積 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  (M : C) [MonObj M]

/-- 右テンソルの作用を交換同型で左テンソルへ移す。 -/
@[instance_reducible] def tensorLeftAction (X : C) (E : Mod C M) : ModObj M (X ⊗ E.X) := by
  letI := tensorRightAction M E X
  have : IsMonHom (Iso.refl M).hom := inferInstanceAs (IsMonHom (𝟙 M))
  exact ModObj.ofIso (Iso.refl M) (β_ E.X X)

/-- 対象を加群の左にテンソルし、交換で移した作用を与える。 -/
def tensorLeftObj (X : C) (E : Mod C M) : Mod C M :=
  letI := tensorLeftAction M X E
  ⟨X ⊗ E.X⟩

/-- 左に移したテンソルの作用の具体式。 -/
lemma tensorLeftObj_action (X : C) (E : Mod C M) :
    γ[M,(tensorLeftObj M X E).X] = M ◁ (β_ E.X X).inv ≫
      (α_ M E.X X).inv ≫ γ[M,E.X] ▷ X ≫ (β_ E.X X).hom := by
  change (𝟙 M ⊗ₘ (β_ E.X X).inv) ≫
    ((α_ M E.X X).inv ≫ γ[M,E.X] ▷ X) ≫ (β_ E.X X).hom = _
  rw [id_tensorHom, Category.assoc]

/-- 加群の左右の通常のテンソルを比較する交換同型。 -/
def tensorLeftIso (E : Mod C M) (X : C) : tensorRightObj M E X ≅ tensorLeftObj M X E := by
  letI : ModObj M (E.X ⊗ X) := tensorRightAction M E X
  letI : ModObj M (X ⊗ E.X) := tensorLeftAction M X E
  have : IsModHom M (β_ E.X X).hom := ⟨by
    change ((α_ M E.X X).inv ≫ γ[M,E.X] ▷ X) ≫ (β_ E.X X).hom =
      M ◁ (β_ E.X X).hom ≫ ((𝟙 M ⊗ₘ (β_ E.X X).inv) ≫
        ((α_ M E.X X).inv ≫ γ[M,E.X] ▷ X) ≫ (β_ E.X X).hom)
    rw [id_tensorHom]
    simp only [Category.assoc, ← whiskerLeft_comp_assoc, Iso.hom_inv_id,
      whiskerLeft_id, Category.id_comp]⟩
  have : IsModHom M (β_ E.X X).inv := inferInstance
  exact {
    hom := Mod.Hom.mk' (β_ E.X X).hom IsModHom.smul_hom
    inv := Mod.Hom.mk' (β_ E.X X).inv IsModHom.smul_hom
    hom_inv_id := Mod.hom_ext _ _ (β_ E.X X).hom_inv_id
    inv_hom_id := Mod.hom_ext _ _ (β_ E.X X).inv_hom_id }

/-- 左テンソルの射を、右テンソルの射と交換同型から構成する。 -/
def tensorLeftMap {X Y : C} (g : X ⟶ Y) {E E' : Mod C M} (f : E ⟶ E') :
    tensorLeftObj M X E ⟶ tensorLeftObj M Y E' :=
  (tensorLeftIso M E X).inv ≫ tensorRightMap M f g ≫ (tensorLeftIso M E' Y).hom

/-- 左テンソルの射の基礎射は通常のテンソル射。 -/
lemma tensorLeftMap_hom {X Y : C} (g : X ⟶ Y) {E E' : Mod C M} (f : E ⟶ E') :
    (tensorLeftMap M g f).hom = g ⊗ₘ f.hom := by
  change (β_ E.X X).inv ≫ (f.hom ⊗ₘ g) ≫ (β_ E'.X Y).hom = _
  rw [BraidedCategory.braiding_naturality, Iso.inv_hom_id_assoc]

variable [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]

/-- 自由加群を左因子とする釣り合い積は、生成対象を加群の左へテンソルした加群と同型。 -/
def freeLeftIso (X : C) (E : Mod C M) :
    moduleObj M (MonoidalFreeModule.freeObj M X) E ≅ tensorLeftObj M X E :=
  swapIso M (MonoidalFreeModule.freeObj M X) E ≪≫ freeRightIso M E X ≪≫ tensorLeftIso M E X

/-- 左自由因子の比較は生成対象と加群の射の両方に関して自然。 -/
lemma freeLeft_naturality {X Y : C} (g : X ⟶ Y) {E E' : Mod C M} (f : E ⟶ E') :
    moduleMap M (MonoidalFreeModule.freeMap M g) f ≫ (freeLeftIso M Y E').hom =
      (freeLeftIso M X E).hom ≫ tensorLeftMap M g f := by
  simp only [freeLeftIso, Iso.trans_hom, tensorLeftMap, Category.assoc,
    Iso.hom_inv_id_assoc]
  slice_lhs 1 2 => rw [swap_naturality]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [freeRight_naturality]
  simp only [Category.assoc]

/-- 左自由因子の比較の逆射は生成元を第一因子へ挿入する。 -/
lemma freeLeftIso_inv (X : C) (E : Mod C M) :
    (freeLeftIso M X E).inv.hom = MonoidalFreeModule.generator M X ▷ E.X ≫
      projection M (MonoidalFreeModule.freeObj M X) E := by
  simp only [freeLeftIso, Iso.trans_inv, Mod.comp_hom', freeRightIso_inv, freeRightInv,
    Category.assoc]
  change (β_ E.X X).inv ≫ E.X ◁ MonoidalFreeModule.generator M X ≫
      projection M E (MonoidalFreeModule.freeObj M X) ≫
        swapHom M E (MonoidalFreeModule.freeObj M X) = _
  rw [projection_swapHom, BraidedCategory.braiding_naturality_right_assoc,
    Iso.inv_hom_id_assoc]

/-- 左自由因子の比較は生成元上で恒等射になる。 -/
@[reassoc] lemma generator_freeLeft_hom (X : C) (E : Mod C M) :
    MonoidalFreeModule.generator M X ▷ E.X ≫
        projection M (MonoidalFreeModule.freeObj M X) E ≫ (freeLeftIso M X E).hom.hom =
      𝟙 (X ⊗ E.X) := by
  rw [← Category.assoc, ← freeLeftIso_inv]
  exact congrArg Mod.Hom.hom (freeLeftIso M X E).inv_hom_id

/-- 自由加群を左因子とする釣り合いテンソル積の二変数関手。 -/
def freeLeftBifunctor : C × Mod C M ⥤ Mod C M :=
  (MonoidalFreeModule.freeFunctor M).prod (𝟭 (Mod C M)) ⋙ moduleBifunctor M

/-- 加群の左に対象をテンソルする二変数関手。 -/
def tensorLeftBifunctor : C × Mod C M ⥤ Mod C M where
  obj XE := tensorLeftObj M XE.1 XE.2
  map gf := tensorLeftMap M gf.1 gf.2
  map_id XE := by
    apply Mod.hom_ext
    rw [tensorLeftMap_hom, Mod.id_hom']
    exact id_tensorHom_id _ _
  map_comp gf hk := by
    apply Mod.hom_ext
    rw [Mod.comp_hom', tensorLeftMap_hom, tensorLeftMap_hom, tensorLeftMap_hom]
    change (gf.1 ≫ hk.1) ⊗ₘ (gf.2.hom ≫ hk.2.hom) = _
    exact (tensorHom_comp_tensorHom _ _ _ _).symm

/-- 左自由因子の比較を二変数の自然同型へまとめる。 -/
def freeLeftNatIso : freeLeftBifunctor M ≅ tensorLeftBifunctor M :=
  NatIso.ofComponents (fun XE => freeLeftIso M XE.1 XE.2)
    (fun gf => freeLeft_naturality M gf.1 gf.2)

end SerrePositivity.MonoidalBalancedTensor
