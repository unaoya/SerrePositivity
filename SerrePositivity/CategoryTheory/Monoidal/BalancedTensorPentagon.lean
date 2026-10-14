module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorAssociator

/-! # 釣り合いテンソル積のpentagon整合性 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : C) [MonObj M] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 四因子を全て左結合した商への標準射。 -/
def quadrupleLeftProjection (E F G H : Mod C M) :
    ((E.X ⊗ F.X) ⊗ G.X) ⊗ H.X ⟶ obj M (moduleObj M (moduleObj M E F) G) H :=
  tripleLeftProjection M E F G ▷ H.X ≫ projection M (moduleObj M (moduleObj M E F) G) H

/-- 四因子を全て右結合した商への標準射。 -/
def quadrupleRightProjection (E F G H : Mod C M) :
    E.X ⊗ (F.X ⊗ (G.X ⊗ H.X)) ⟶ obj M E (moduleObj M F (moduleObj M G H)) :=
  E.X ◁ tripleRightProjection M F G H ≫ projection M E (moduleObj M F (moduleObj M G H))

/-- 二つずつ組にした四因子の商への標準射。 -/
def quadrupleMiddleProjection (E F G H : Mod C M) :
    (E.X ⊗ F.X) ⊗ (G.X ⊗ H.X) ⟶ obj M (moduleObj M E F) (moduleObj M G H) :=
  (projection M E F ⊗ₘ projection M G H) ≫
    projection M (moduleObj M E F) (moduleObj M G H)

/-- pentagonの上側の中間の結合順への標準射。 -/
def pentagonUpperProjection (E F G H : Mod C M) :
    (E.X ⊗ (F.X ⊗ G.X)) ⊗ H.X ⟶ obj M (moduleObj M E (moduleObj M F G)) H :=
  (E.X ◁ projection M F G) ▷ H.X ≫ tripleLeftProjection M E (moduleObj M F G) H

/-- pentagonの下側の中間の結合順への標準射。 -/
def pentagonLowerProjection (E F G H : Mod C M) :
    E.X ⊗ ((F.X ⊗ G.X) ⊗ H.X) ⟶ obj M E (moduleObj M (moduleObj M F G) H) :=
  E.X ◁ tripleLeftProjection M F G H ≫ projection M E (moduleObj M (moduleObj M F G) H)

/-- 左結合した四因子の標準射はエピ射。 -/
instance quadrupleLeftProjection_epi (E F G H : Mod C M) :
    Epi (quadrupleLeftProjection M E F G H) := by
  have : Epi ((projection M E F ▷ G.X) ▷ H.X) := inferInstanceAs
    (Epi (((tensorRight G.X) ⋙ tensorRight H.X).map
      (coequalizer.π (relationLeft M E F) (relationRight M E F))))
  unfold quadrupleLeftProjection tripleLeftProjection
  rw [comp_whiskerRight]
  infer_instance

/-- 上側の第一の結合変更の標準射上の計算。 -/
@[reassoc] lemma quadrupleLeftProjection_map_associator (E F G H : Mod C M) :
    quadrupleLeftProjection M E F G H ≫ map M (associatorIso M E F G).hom (𝟙 H) =
      (α_ E.X F.X G.X).hom ▷ H.X ≫ pentagonUpperProjection M E F G H := by
  rw [quadrupleLeftProjection, Category.assoc, projection_map]
  change tripleLeftProjection M E F G ▷ H.X ≫
    (associatorHom M E F G ⊗ₘ 𝟙 H.X) ≫ projection M (moduleObj M E (moduleObj M F G)) H = _
  rw [tensorHom_id, ← comp_whiskerRight_assoc, tripleLeftProjection_associatorHom,
    comp_whiskerRight]
  simp only [tripleRightProjection, comp_whiskerRight, pentagonUpperProjection,
    tripleLeftProjection, Category.assoc]

/-- 上側の第二の結合変更の標準射上の計算。 -/
@[reassoc] lemma pentagonUpperProjection_associator (E F G H : Mod C M) :
    pentagonUpperProjection M E F G H ≫ associatorHom M E (moduleObj M F G) H =
      (α_ E.X (F.X ⊗ G.X) H.X).hom ≫ pentagonLowerProjection M E F G H := by
  rw [pentagonUpperProjection, Category.assoc, tripleLeftProjection_associatorHom]
  erw [associator_naturality_middle_assoc]
  simp only [tripleRightProjection, pentagonLowerProjection, tripleLeftProjection,
    whiskerLeft_comp, Category.assoc]

/-- 上側の第三の結合変更の標準射上の計算。 -/
@[reassoc] lemma pentagonLowerProjection_map_associator (E F G H : Mod C M) :
    pentagonLowerProjection M E F G H ≫ map M (𝟙 E) (associatorIso M F G H).hom =
      E.X ◁ (α_ F.X G.X H.X).hom ≫ quadrupleRightProjection M E F G H := by
  rw [pentagonLowerProjection, Category.assoc, projection_map]
  change E.X ◁ tripleLeftProjection M F G H ≫
    (𝟙 E.X ⊗ₘ associatorHom M F G H) ≫ projection M E (moduleObj M F (moduleObj M G H)) = _
  rw [id_tensorHom, ← whiskerLeft_comp_assoc, tripleLeftProjection_associatorHom,
    whiskerLeft_comp]
  simp only [quadrupleRightProjection, Category.assoc]

/-- 下側の第一の結合変更の標準射上の計算。 -/
@[reassoc] lemma quadrupleLeftProjection_associator (E F G H : Mod C M) :
    quadrupleLeftProjection M E F G H ≫ associatorHom M (moduleObj M E F) G H =
      (α_ (E.X ⊗ F.X) G.X H.X).hom ≫ quadrupleMiddleProjection M E F G H := by
  simp only [quadrupleLeftProjection, tripleLeftProjection, comp_whiskerRight, Category.assoc]
  rw [associatorHom, projection_desc, projection_associatorStep]
  erw [associator_naturality_left_assoc]
  simp only [tripleRightProjection, quadrupleMiddleProjection, tensorHom_def, Category.assoc,
    moduleObj_underlying]

/-- 下側の第二の結合変更の標準射上の計算。 -/
@[reassoc] lemma quadrupleMiddleProjection_associator (E F G H : Mod C M) :
    quadrupleMiddleProjection M E F G H ≫ associatorHom M E F (moduleObj M G H) =
      (α_ E.X F.X (G.X ⊗ H.X)).hom ≫ quadrupleRightProjection M E F G H := by
  simp only [quadrupleMiddleProjection, tensorHom_def, Category.assoc]
  rw [← whisker_exchange_assoc]
  rw [associatorHom, projection_desc]
  change (E.X ⊗ F.X) ◁ projection M G H ≫
    projection M E F ▷ (moduleObj M G H).X ≫ associatorStep M E F (moduleObj M G H) = _
  rw [projection_associatorStep]
  erw [associator_naturality_right_assoc]
  simp only [tripleRightProjection, quadrupleRightProjection, whiskerLeft_comp, Category.assoc]

/-- 釣り合いテンソル積の結合同型はpentagon整合性を満たす。 -/
lemma pentagon (E F G H : Mod C M) :
    moduleMap M (associatorIso M E F G).hom (𝟙 H) ≫
        (associatorIso M E (moduleObj M F G) H).hom ≫
          moduleMap M (𝟙 E) (associatorIso M F G H).hom =
      (associatorIso M (moduleObj M E F) G H).hom ≫
        (associatorIso M E F (moduleObj M G H)).hom := by
  apply Mod.hom_ext
  apply (cancel_epi (quadrupleLeftProjection M E F G H)).1
  change quadrupleLeftProjection M E F G H ≫
      map M (associatorIso M E F G).hom (𝟙 H) ≫ associatorHom M E (moduleObj M F G) H ≫
        map M (𝟙 E) (associatorIso M F G H).hom =
    quadrupleLeftProjection M E F G H ≫ associatorHom M (moduleObj M E F) G H ≫
      associatorHom M E F (moduleObj M G H)
  rw [quadrupleLeftProjection_map_associator_assoc, pentagonUpperProjection_associator_assoc,
    pentagonLowerProjection_map_associator, quadrupleLeftProjection_associator_assoc,
    quadrupleMiddleProjection_associator, MonoidalCategory.pentagon_assoc]

end SerrePositivity.MonoidalBalancedTensor
