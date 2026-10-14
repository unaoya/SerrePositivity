module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorIterated

/-! # 釣り合いテンソル積の結合比較 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : C) [MonObj M] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 右結合の標準射は、左側の二因子の釣り合い関係式と両立する。 -/
lemma associatorSeed_balanced (E F G : Mod C M) :
    relationLeft M E F ▷ G.X ≫ (α_ E.X F.X G.X).hom ≫ tripleRightProjection M E F G =
      relationRight M E F ▷ G.X ≫ (α_ E.X F.X G.X).hom ≫
        tripleRightProjection M E F G := by
  simp only [relationLeft, relationRight, tripleRightProjection, comp_whiskerRight,
    Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc]
  have h := projection_condition M E (moduleObj M F G)
  change rightActionMap M E ▷ (obj M F G) ≫ projection M E (moduleObj M F G) =
    ((α_ E.X M (obj M F G)).hom ≫ E.X ◁ γ[M,(moduleObj M F G).X]) ≫
      projection M E (moduleObj M F G) at h
  erw [h]
  simp only [Category.assoc]
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, projection_action,
    whiskerLeft_comp, whiskerLeft_comp]
  rw [associator_naturality_middle_assoc]
  have hc : (α_ (E.X ⊗ M) F.X G.X).hom ≫ (α_ E.X M (F.X ⊗ G.X)).hom ≫
      E.X ◁ (α_ M F.X G.X).inv =
    (α_ E.X M F.X).hom ▷ G.X ≫ (α_ E.X (M ⊗ F.X) G.X).hom := by monoidal
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ E.X ◁ (γ[M,F.X] ▷ G.X) ≫ E.X ◁ projection M F G ≫
      projection M E (moduleObj M F G)) hc

/-- 左側の二因子の商へ降ろした結合比較の第一段階。 -/
def associatorStep (E F G : Mod C M) : obj M E F ⊗ G.X ⟶ obj M E (moduleObj M F G) :=
  descRight M E F G.X ((α_ E.X F.X G.X).hom ≫ tripleRightProjection M E F G)
    (by simpa only [Category.assoc] using associatorSeed_balanced M E F G)

/-- 第一段階の結合比較は標準射上で基礎圏の結合子に一致する。 -/
@[reassoc] lemma projection_associatorStep (E F G : Mod C M) :
    projection M E F ▷ G.X ≫ associatorStep M E F G =
      (α_ E.X F.X G.X).hom ≫ tripleRightProjection M E F G := projection_descRight M _ _ _ _ _

/-- 第一段階の比較は残る二因子の釣り合い条件も満たす。 -/
lemma associatorStep_balanced (E F G : Mod C M) :
    relationLeft M (moduleObj M E F) G ≫ associatorStep M E F G =
      relationRight M (moduleObj M E F) G ≫ associatorStep M E F G := by
  have : Epi ((projection M E F ▷ M) ▷ G.X) := inferInstanceAs
    (Epi (((tensorRight M) ⋙ tensorRight G.X).map
      (coequalizer.π (relationLeft M E F) (relationRight M E F))))
  apply (cancel_epi ((projection M E F ▷ M) ▷ G.X)).1
  simp only [relationLeft, relationRight, Category.assoc]
  change (projection M E F ▷ M) ▷ G.X ≫
      rightActionMap M (moduleObj M E F) ▷ G.X ≫ associatorStep M E F G =
    (projection M E F ▷ M) ▷ G.X ≫ (α_ (obj M E F) M G.X).hom ≫
      (obj M E F) ◁ γ[M,G.X] ≫ associatorStep M E F G
  rw [← comp_whiskerRight_assoc, projection_rightAction, comp_whiskerRight,
    comp_whiskerRight, Category.assoc, Category.assoc, projection_associatorStep,
    associator_naturality_middle_assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, projection_associatorStep,
    associator_naturality_right_assoc]
  simp only [tripleRightProjection]
  rw [← whiskerLeft_comp_assoc]
  have h := projection_condition M F G
  change rightActionMap M F ▷ G.X ≫ projection M F G =
    ((α_ F.X M G.X).hom ≫ F.X ◁ γ[M,G.X]) ≫ projection M F G at h
  rw [h, whiskerLeft_comp, whiskerLeft_comp]
  have hc : (α_ E.X F.X M).hom ▷ G.X ≫ (α_ E.X (F.X ⊗ M) G.X).hom ≫
      E.X ◁ (α_ F.X M G.X).hom =
    (α_ (E.X ⊗ F.X) M G.X).hom ≫ (α_ E.X F.X (M ⊗ G.X)).hom := by monoidal
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ E.X ◁ F.X ◁ γ[M,G.X] ≫ E.X ◁ projection M F G ≫
      projection M E (moduleObj M F G)) hc

/-- 二段の釣り合い商へ降ろした結合比較の順方向。 -/
def associatorHom (E F G : Mod C M) :
    obj M (moduleObj M E F) G ⟶ obj M E (moduleObj M F G) :=
  desc M ⟨associatorStep M E F G, associatorStep_balanced M E F G⟩

/-- 結合比較の順方向は三つの因子からの標準射上で結合子に一致する。 -/
@[reassoc] lemma tripleLeftProjection_associatorHom (E F G : Mod C M) :
    tripleLeftProjection M E F G ≫ associatorHom M E F G =
      (α_ E.X F.X G.X).hom ≫ tripleRightProjection M E F G := by
  rw [tripleLeftProjection, Category.assoc, associatorHom, projection_desc,
    projection_associatorStep]

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 左結合の標準射は右側の二因子の釣り合い関係式と両立する。 -/
lemma associatorInvSeed_balanced (E F G : Mod C M) :
    E.X ◁ relationLeft M F G ≫ (α_ E.X F.X G.X).inv ≫ tripleLeftProjection M E F G =
      E.X ◁ relationRight M F G ≫ (α_ E.X F.X G.X).inv ≫
        tripleLeftProjection M E F G := by
  simp only [relationLeft, relationRight, tripleLeftProjection, whiskerLeft_comp,
    Category.assoc]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc]
  have h : E.X ◁ rightActionMap M F ≫ projection M E F =
      (α_ E.X F.X M).inv ≫ projection M E F ▷ M ≫
        rightActionMap M (moduleObj M E F) := by
    rw [projection_rightAction, Iso.inv_hom_id_assoc]
  rw [h, comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  have hc := projection_condition M (moduleObj M E F) G
  change rightActionMap M (moduleObj M E F) ▷ G.X ≫ projection M (moduleObj M E F) G =
    ((α_ (obj M E F) M G.X).hom ≫ (obj M E F) ◁ γ[M,G.X]) ≫
      projection M (moduleObj M E F) G at hc
  erw [hc]
  simp only [Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc]
  rw [associator_inv_naturality_right_assoc]
  have hk : (α_ E.X (F.X ⊗ M) G.X).inv ≫ (α_ E.X F.X M).inv ▷ G.X ≫
      (α_ (E.X ⊗ F.X) M G.X).hom =
    E.X ◁ (α_ F.X M G.X).hom ≫ (α_ E.X F.X (M ⊗ G.X)).inv := by monoidal
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ (E.X ⊗ F.X) ◁ γ[M,G.X] ≫ projection M E F ▷ G.X ≫
      projection M (moduleObj M E F) G) hk

/-- 右側の二因子の商へ降ろした逆結合比較の第一段階。 -/
def associatorInvStep (E F G : Mod C M) : E.X ⊗ obj M F G ⟶ obj M (moduleObj M E F) G :=
  descLeft M E.X F G ((α_ E.X F.X G.X).inv ≫ tripleLeftProjection M E F G)
    (by simpa only [Category.assoc] using associatorInvSeed_balanced M E F G)

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 逆比較の第一段階は標準射上で結合子の逆に一致する。 -/
@[reassoc] lemma projection_associatorInvStep (E F G : Mod C M) :
    E.X ◁ projection M F G ≫ associatorInvStep M E F G =
      (α_ E.X F.X G.X).inv ≫ tripleLeftProjection M E F G :=
  projection_descLeft M _ _ _ _ _

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 逆比較の第一段階は残る二因子の釣り合い条件も満たす。 -/
lemma associatorInvStep_balanced (E F G : Mod C M) :
    relationLeft M E (moduleObj M F G) ≫ associatorInvStep M E F G =
      relationRight M E (moduleObj M F G) ≫ associatorInvStep M E F G := by
  have : Epi ((E.X ⊗ M) ◁ projection M F G) := inferInstance
  apply (cancel_epi ((E.X ⊗ M) ◁ projection M F G)).1
  simp only [relationLeft, relationRight, Category.assoc]
  change (E.X ⊗ M) ◁ projection M F G ≫ rightActionMap M E ▷ (obj M F G) ≫
      associatorInvStep M E F G =
    (E.X ⊗ M) ◁ projection M F G ≫ (α_ E.X M (obj M F G)).hom ≫
      E.X ◁ γ[M,(moduleObj M F G).X] ≫ associatorInvStep M E F G
  rw [whisker_exchange_assoc, projection_associatorInvStep,
    associator_inv_naturality_left_assoc, associator_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, projection_action, whiskerLeft_comp, whiskerLeft_comp]
  rw [Category.assoc, Category.assoc, projection_associatorInvStep]
  erw [associator_inv_naturality_middle_assoc]
  simp only [tripleLeftProjection]
  rw [← comp_whiskerRight_assoc]
  have h := projection_condition M E F
  change rightActionMap M E ▷ F.X ≫ projection M E F =
    ((α_ E.X M F.X).hom ≫ E.X ◁ γ[M,F.X]) ≫ projection M E F at h
  rw [h, comp_whiskerRight, comp_whiskerRight]
  have hk : (α_ (E.X ⊗ M) F.X G.X).inv ≫ (α_ E.X M F.X).hom ▷ G.X =
    (α_ E.X M (F.X ⊗ G.X)).hom ≫ E.X ◁ (α_ M F.X G.X).inv ≫
      (α_ E.X (M ⊗ F.X) G.X).inv := by monoidal
  simpa only [Category.assoc, MonoidalLeftActionStruct.actionObj] using congrArg
    (fun k => k ≫ (E.X ◁ γ[M,F.X]) ▷ G.X ≫ projection M E F ▷ G.X ≫
      projection M (moduleObj M E F) G) hk

/-- 二段の釣り合い商へ降ろした結合比較の逆方向。 -/
def associatorInv (E F G : Mod C M) :
    obj M E (moduleObj M F G) ⟶ obj M (moduleObj M E F) G :=
  desc M ⟨associatorInvStep M E F G, associatorInvStep_balanced M E F G⟩

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 結合比較の逆方向は三つの因子からの標準射上で結合子の逆に一致する。 -/
@[reassoc] lemma tripleRightProjection_associatorInv (E F G : Mod C M) :
    tripleRightProjection M E F G ≫ associatorInv M E F G =
      (α_ E.X F.X G.X).inv ≫ tripleLeftProjection M E F G := by
  rw [tripleRightProjection, Category.assoc, associatorInv, projection_desc,
    projection_associatorInvStep]

/-- 反復釣り合いテンソル積の基礎対象の結合同型。 -/
def associatorUnderlyingIso (E F G : Mod C M) :
    obj M (moduleObj M E F) G ≅ obj M E (moduleObj M F G) where
  hom := associatorHom M E F G
  inv := associatorInv M E F G
  hom_inv_id := by
    apply (cancel_epi (tripleLeftProjection M E F G)).1
    rw [tripleLeftProjection_associatorHom_assoc, tripleRightProjection_associatorInv,
      Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    apply (cancel_epi (tripleRightProjection M E F G)).1
    rw [tripleRightProjection_associatorInv_assoc, tripleLeftProjection_associatorHom,
      Iso.inv_hom_id_assoc, Category.comp_id]

/-- 左結合の三因子の標準射を、加群の射として構成する。 -/
def tripleLeftModuleHom (E F G : Mod C M) :
    tensorRightObj M (tensorRightObj M E F.X) G.X ⟶ moduleObj M (moduleObj M E F) G :=
  tensorRightMap M (projectionModuleHom M E F) (𝟙 G.X) ≫
    projectionModuleHom M (moduleObj M E F) G

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 左結合の三因子の標準射の加群としての基礎射。 -/
lemma tripleLeftModuleHom_hom (E F G : Mod C M) :
    (tripleLeftModuleHom M E F G).hom = tripleLeftProjection M E F G := by
  change (projection M E F ⊗ₘ 𝟙 G.X) ≫ projection M (moduleObj M E F) G = _
  rw [tensorHom_id]
  rfl

/-- 右結合の三因子の標準射を、加群の射として構成する。 -/
def tripleRightModuleHom (E F G : Mod C M) :
    tensorRightObj M E (F.X ⊗ G.X) ⟶ moduleObj M E (moduleObj M F G) :=
  tensorRightMap M (𝟙 E) (projection M F G) ≫ projectionModuleHom M E (moduleObj M F G)

omit [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)] in
/-- 右結合の三因子の標準射の加群としての基礎射。 -/
lemma tripleRightModuleHom_hom (E F G : Mod C M) :
    (tripleRightModuleHom M E F G).hom = tripleRightProjection M E F G := by
  change (𝟙 E.X ⊗ₘ projection M F G) ≫ projection M E (moduleObj M F G) = _
  rw [id_tensorHom]
  rfl

/-- 結合比較の順方向は加群作用と両立する。 -/
def associatorModuleHom (E F G : Mod C M) :
    moduleObj M (moduleObj M E F) G ⟶ moduleObj M E (moduleObj M F G) :=
  Mod.Hom.mk' (associatorHom M E F G) (by
    have : Epi (M ◁ (projection M E F ▷ G.X)) := inferInstanceAs
      (Epi (((tensorRight G.X) ⋙ tensorLeft M).map
        (coequalizer.π (relationLeft M E F) (relationRight M E F))))
    have : Epi (M ◁ tripleLeftProjection M E F G) := by
      unfold tripleLeftProjection
      rw [whiskerLeft_comp]
      infer_instance
    apply (cancel_epi (M ◁ tripleLeftProjection M E F G)).1
    have hl := IsModHom.smul_hom (A := M) (f := (tripleLeftModuleHom M E F G).hom)
    rw [tripleLeftModuleHom_hom] at hl
    change γ[M,(tensorRightObj M (tensorRightObj M E F.X) G.X).X] ≫
        tripleLeftProjection M E F G =
      M ◁ tripleLeftProjection M E F G ≫
        γ[M,(moduleObj M (moduleObj M E F) G).X] at hl
    let seed := tensorRightAssociator M E F.X G.X ≫ tripleRightModuleHom M E F G
    have hs := IsModHom.smul_hom (A := M) (f := seed.hom)
    change γ[M,(tensorRightObj M (tensorRightObj M E F.X) G.X).X] ≫
        ((α_ E.X F.X G.X).hom ≫ (tripleRightModuleHom M E F G).hom) =
      M ◁ ((α_ E.X F.X G.X).hom ≫ (tripleRightModuleHom M E F G).hom) ≫
        γ[M,(moduleObj M E (moduleObj M F G)).X] at hs
    rw [tripleRightModuleHom_hom] at hs
    change M ◁ tripleLeftProjection M E F G ≫
        γ[M,(moduleObj M (moduleObj M E F) G).X] ≫ associatorHom M E F G =
      M ◁ tripleLeftProjection M E F G ≫ M ◁ associatorHom M E F G ≫
        γ[M,(moduleObj M E (moduleObj M F G)).X]
    rw [← Category.assoc, ← hl, Category.assoc, tripleLeftProjection_associatorHom,
      ← whiskerLeft_comp_assoc, tripleLeftProjection_associatorHom]
    exact hs)

/-- 反復釣り合いテンソル積の加群としての結合同型。 -/
def associatorIso (E F G : Mod C M) :
    moduleObj M (moduleObj M E F) G ≅ moduleObj M E (moduleObj M F G) := by
  let i := associatorUnderlyingIso M E F G
  letI : ModObj M (obj M (moduleObj M E F) G) := (moduleObj M (moduleObj M E F) G).mod
  letI : ModObj M (obj M E (moduleObj M F G)) := (moduleObj M E (moduleObj M F G)).mod
  have : IsModHom M i.hom := (associatorModuleHom M E F G).isModHom
  have : IsModHom M i.inv := inferInstance
  exact {
    hom := associatorModuleHom M E F G
    inv := Mod.Hom.mk' i.inv IsModHom.smul_hom
    hom_inv_id := Mod.hom_ext _ _ i.hom_inv_id
    inv_hom_id := Mod.hom_ext _ _ i.inv_hom_id }

/-- 加群としての結合同型の順方向の基礎射。 -/
lemma associatorIso_hom (E F G : Mod C M) :
    (associatorIso M E F G).hom.hom = associatorHom M E F G := rfl

/-- 加群としての結合同型の逆方向の基礎射。 -/
lemma associatorIso_inv (E F G : Mod C M) :
    (associatorIso M E F G).inv.hom = associatorInv M E F G := rfl

/-- 結合同型は三つの加群の射に関して自然。 -/
lemma associator_naturality {E E' F F' G G' : Mod C M}
    (f : E ⟶ E') (g : F ⟶ F') (h : G ⟶ G') :
    moduleMap M (moduleMap M f g) h ≫ (associatorIso M E' F' G').hom =
      (associatorIso M E F G).hom ≫ moduleMap M f (moduleMap M g h) := by
  apply Mod.hom_ext
  apply (cancel_epi (tripleLeftProjection M E F G)).1
  change tripleLeftProjection M E F G ≫ map M (moduleMap M f g) h ≫
      associatorHom M E' F' G' =
    tripleLeftProjection M E F G ≫ associatorHom M E F G ≫ map M f (moduleMap M g h)
  rw [tripleLeftProjection_map_assoc, tripleLeftProjection_associatorHom,
    tripleLeftProjection_associatorHom_assoc, tripleRightProjection_map]
  rw [CategoryTheory.MonoidalCategory.associator_naturality_assoc]

/-- 三つの入力の組を右結合へ並べ直す関手。 -/
def tripleReassociate : (Mod C M × Mod C M) × Mod C M ⥤ Mod C M × (Mod C M × Mod C M) where
  obj EFG := (EFG.1.1, (EFG.1.2, EFG.2))
  map fgh := (fgh.1.1, (fgh.1.2, fgh.2))

/-- 左結合した釣り合いテンソル積の三変数関手。 -/
def tripleLeftFunctor : (Mod C M × Mod C M) × Mod C M ⥤ Mod C M :=
  (moduleBifunctor M).prod (𝟭 (Mod C M)) ⋙ moduleBifunctor M

/-- 右結合した釣り合いテンソル積の三変数関手。 -/
def tripleRightFunctor : (Mod C M × Mod C M) × Mod C M ⥤ Mod C M :=
  tripleReassociate M ⋙ (𝟭 (Mod C M)).prod (moduleBifunctor M) ⋙ moduleBifunctor M

/-- 反復釣り合いテンソル積の三変数の結合自然同型。 -/
def associatorNatIso : tripleLeftFunctor M ≅ tripleRightFunctor M :=
  NatIso.ofComponents (fun EFG => associatorIso M EFG.1.1 EFG.1.2 EFG.2)
    (fun fgh => associator_naturality M fgh.1.1 fgh.1.2 fgh.2)

end SerrePositivity.MonoidalBalancedTensor
