module

public import SerrePositivity.CategoryTheory.Monoidal.TensorRightModule
public import SerrePositivity.CategoryTheory.Monoidal.ModuleColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # 可換モノイド上の釣り合いテンソル積の加群作用

釣り合い関係式を加群の射へ持ち上げ、基礎対象の余等化子へ作用を降ろす。
作用の法則は加群の余極限の一般論から得る。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : C) [MonObj M] [IsCommMonObj M]

/-- 釣り合い関係式の左辺は加群の射となる。 -/
def relationLeftHom (E F : Mod C M) :
    tensorRightObj M (tensorRightObj M E M) F.X ⟶ tensorRightObj M E F.X :=
  Mod.Hom.mk' (relationLeft M E F) (by
    change γ[M,(tensorRightObj M (tensorRightObj M E M) F.X).X] ≫ relationLeft M E F =
      M ◁ relationLeft M E F ≫ γ[M,(tensorRightObj M E F.X).X]
    have h : γ[M,(tensorRightObj M (tensorRightObj M E M) F.X).X] ≫
        (rightActionMap M E ⊗ₘ 𝟙 F.X) =
      M ◁ (rightActionMap M E ⊗ₘ 𝟙 F.X) ≫ γ[M,(tensorRightObj M E F.X).X] :=
      IsModHom.smul_hom (A := M) (f := (tensorRightMap M (rightActionHom M E) (𝟙 F.X)).hom)
    simpa only [tensorHom_id, relationLeft] using h)

/-- 釣り合い関係式の右辺は加群の射となる。 -/
def relationRightHom (E F : Mod C M) :
    tensorRightObj M (tensorRightObj M E M) F.X ⟶ tensorRightObj M E F.X :=
  Mod.Hom.mk' (relationRight M E F) (by
    change γ[M,(tensorRightObj M (tensorRightObj M E M) F.X).X] ≫ relationRight M E F =
      M ◁ relationRight M E F ≫ γ[M,(tensorRightObj M E F.X).X]
    have h : γ[M,(tensorRightObj M (tensorRightObj M E M) F.X).X] ≫
        ((α_ E.X M F.X).hom ≫ (𝟙 E.X ⊗ₘ γ[M,F.X])) =
      M ◁ ((α_ E.X M F.X).hom ≫ (𝟙 E.X ⊗ₘ γ[M,F.X])) ≫
        γ[M,(tensorRightObj M E F.X).X] :=
      IsModHom.smul_hom (A := M)
        (f := (tensorRightAssociator M E M F.X ≫ tensorRightMap M (𝟙 E) γ[M,F.X]).hom)
    simpa only [id_tensorHom, relationRight] using h)

/-- 釣り合いテンソル積を作る加群圏の平行射の図式。 -/
def moduleDiagram (E F : Mod C M) : WalkingParallelPair ⥤ Mod C M :=
  parallelPair (relationLeftHom M E F) (relationRightHom M E F)

/-- 平行射の忘却像は既存の釣り合い関係式の図式。 -/
def underlyingDiagramIso (E F : Mod C M) :
    moduleDiagram M E F ⋙ Mod.forget M ≅ parallelPair (relationLeft M E F) (relationRight M E F) :=
  NatIso.ofComponents (fun j => by cases j <;> exact Iso.refl _) (by
    rintro j k f
    cases f with
    | left => simp [moduleDiagram, relationLeftHom]
    | right => simp [moduleDiagram, relationRightHom]
    | id j => cases j <;> simp [moduleDiagram] <;> rfl)

variable [HasCoequalizers C]

/-- 加群図式の忘却像に対する、既存の釣り合い商の余錐。 -/
def underlyingCocone (E F : Mod C M) : Cocone (moduleDiagram M E F ⋙ Mod.forget M) :=
  (Cocone.precompose (underlyingDiagramIso M E F).hom).obj
    (Cofork.ofπ (projection M E F) (projection_condition M E F))

/-- 既存の釣り合い商の余錐は忘却像の余極限。 -/
def underlyingCoconeIsColimit (E F : Mod C M) : IsColimit (underlyingCocone M E F) :=
  (IsColimit.precomposeHomEquiv (underlyingDiagramIso M E F)
    (Cofork.ofπ (projection M E F) (projection_condition M E F))).symm
      (coequalizerIsCoequalizer (relationLeft M E F) (relationRight M E F))

/-- 忘却像の余錐の標準包含は既存の商への標準射。 -/
@[simp] lemma underlyingCocone_ι_one (E F : Mod C M) :
    (underlyingCocone M E F).ι.app WalkingParallelPair.one = projection M E F := by
  simp [underlyingCocone, underlyingDiagramIso]

variable [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]

/-- 釣り合い商上へ作用を降ろした内部加群。 -/
def moduleObj (E F : Mod C M) : Mod C M :=
  MonoidalModuleColimits.colimitObj M (moduleDiagram M E F) (underlyingCocone M E F)
    (underlyingCoconeIsColimit M E F)

/-- 構成した加群の基礎対象は既存の釣り合い商そのもの。 -/
lemma moduleObj_underlying (E F : Mod C M) : (moduleObj M E F).X = obj M E F := rfl

/-- 商の作用は標準射を介して第一因子の作用と両立する。 -/
@[reassoc] lemma projection_action (E F : Mod C M) :
    M ◁ projection M E F ≫ γ[M,(moduleObj M E F).X] =
      (α_ M E.X F.X).inv ≫ γ[M,E.X] ▷ F.X ≫ projection M E F := by
  have h := MonoidalModuleColimits.colimitSmul_ι M (moduleDiagram M E F)
    (underlyingCocone M E F) (underlyingCoconeIsColimit M E F) WalkingParallelPair.one
  change M ◁ (underlyingCocone M E F).ι.app WalkingParallelPair.one ≫
      γ[M,(moduleObj M E F).X] =
    γ[M,(tensorRightObj M E F.X).X] ≫
      (underlyingCocone M E F).ι.app WalkingParallelPair.one at h
  rw [underlyingCocone_ι_one] at h
  change M ◁ projection M E F ≫ γ[M,(moduleObj M E F).X] =
    ((α_ M E.X F.X).inv ≫ γ[M,E.X] ▷ F.X) ≫ projection M E F at h
  simpa only [Category.assoc] using h

/-- 既存の商の射は、降下した加群作用と両立する。 -/
def moduleMap {E E' F F' : Mod C M} (f : E ⟶ E') (g : F ⟶ F') :
    moduleObj M E F ⟶ moduleObj M E' F' :=
  Mod.Hom.mk' (map M f g) (by
    change γ[M,(moduleObj M E F).X] ≫ map M f g =
      M ◁ map M f g ≫ γ[M,(moduleObj M E' F').X]
    have : Epi (M ◁ projection M E F) := inferInstanceAs
      (Epi ((tensorLeft M).map (coequalizer.π (relationLeft M E F) (relationRight M E F))))
    apply (cancel_epi (M ◁ projection M E F)).1
    rw [projection_action_assoc, projection_map, ← whiskerLeft_comp_assoc,
      projection_map, whiskerLeft_comp, Category.assoc, projection_action]
    have h : γ[M,(tensorRightObj M E F.X).X] ≫ (f.hom ⊗ₘ g.hom) =
        M ◁ (f.hom ⊗ₘ g.hom) ≫ γ[M,(tensorRightObj M E' F'.X).X] :=
      IsModHom.smul_hom (A := M) (f := (tensorRightMap M f g.hom).hom)
    change ((α_ M E.X F.X).inv ≫ γ[M,E.X] ▷ F.X) ≫ (f.hom ⊗ₘ g.hom) =
      M ◁ (f.hom ⊗ₘ g.hom) ≫ ((α_ M E'.X F'.X).inv ≫ γ[M,E'.X] ▷ F'.X) at h
    simpa only [Category.assoc] using congrArg (fun k => k ≫ projection M E' F') h)

/-- 釣り合いテンソル積を加群圏に値を取る二変数関手へまとめる。 -/
def moduleBifunctor : Mod C M × Mod C M ⥤ Mod C M where
  obj EF := moduleObj M EF.1 EF.2
  map fg := moduleMap M fg.1 fg.2
  map_id EF := Mod.hom_ext _ _ (map_id M EF.1 EF.2)
  map_comp fg gh := Mod.hom_ext _ _ (map_comp M fg.1 gh.1 fg.2 gh.2)

/-- 釣り合い射が第一因子の加群作用と両立するとき、加群の射として降ろせる。 -/
def moduleDesc {E F G : Mod C M} (f : BalancedMap M E F G.X)
    (hf : (α_ M E.X F.X).inv ≫ γ[M,E.X] ▷ F.X ≫ f.val =
      M ◁ f.val ≫ γ[M,G.X]) : moduleObj M E F ⟶ G :=
  Mod.Hom.mk' (desc M f) (by
    change γ[M,(moduleObj M E F).X] ≫ desc M f = M ◁ desc M f ≫ γ[M,G.X]
    have : Epi (M ◁ projection M E F) := inferInstanceAs
      (Epi ((tensorLeft M).map (coequalizer.π (relationLeft M E F) (relationRight M E F))))
    apply (cancel_epi (M ◁ projection M E F)).1
    rw [projection_action_assoc, projection_desc, ← whiskerLeft_comp_assoc, projection_desc]
    exact hf)

/-- 加群の射として降下しても、基礎対象の降下は変わらない。 -/
lemma moduleDesc_hom {E F G : Mod C M} (f : BalancedMap M E F G.X)
    (hf : (α_ M E.X F.X).inv ≫ γ[M,E.X] ▷ F.X ≫ f.val =
      M ◁ f.val ≫ γ[M,G.X]) : (moduleDesc M f hf).hom = desc M f := rfl

end SerrePositivity.MonoidalBalancedTensor
