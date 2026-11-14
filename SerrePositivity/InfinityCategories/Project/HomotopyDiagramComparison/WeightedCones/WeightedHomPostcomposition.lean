module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimitHom

/-!
概要：重み付き Hom の切断に全 Hom パラメータで後合成する。
方針：各成分の内部 Hom の豊穣合成を用い、end の自然性を検証する。
規約：後合成のパラメータは任意の単体集合。零単体の射への制限はしない。
使われ方：HTT 4.2.4.1 の coend の普遍切断と比較族の豊穣自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped MonoidalClosed
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- 内部 Hom の恒等射を前合成すると、元の射の単位からの表示になる。 -/
lemma internalHom_id_pre {L K : SSet.{u}} (j : L ⟶ K) :
    MonoidalClosed.id K ≫ (pre j).app K = curry' j := by
  rw [MonoidalClosed.id_eq, curry_pre_app, rightUnitor_naturality]
  rfl

/-- curry した族の豊穣な後合成は、評価を後合成して curry した族に一致する。 -/
lemma internalHom_curry_comp {X A Y Z : SSet.{u}} (e : X ⊗ A ⟶ Y) :
    curry e ▷ (ihom Y).obj Z ≫ MonoidalClosed.comp X Y Z =
      curry ((α_ X A ((ihom Y).obj Z)).inv ≫
        (e ▷ (ihom Y).obj Z) ≫ (ihom.ev Y).app Z) := by
  apply uncurry_injective
  rw [uncurry_natural_left, MonoidalClosed.comp_eq, uncurry_curry,
    MonoidalClosed.compTranspose_eq, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, ← uncurry_eq, uncurry_curry, uncurry_curry]

/-- tensor からの射の Hom への二重転置は全 Hom パラメータの合成を保つ。 -/
lemma internalHom_tensorMap_comp {X W L Y Z : SSet.{u}} (f : X ⊗ W ⟶ L) :
    W ◁ MonoidalClosed.comp L Y Z ≫
        curry ((α_ X W ((ihom L).obj Z)).inv ≫
          (f ▷ (ihom L).obj Z) ≫ (ihom.ev L).app Z) =
      (α_ W ((ihom L).obj Y) ((ihom Y).obj Z)).inv ≫
        curry ((α_ X W ((ihom L).obj Y)).inv ≫
          (f ▷ (ihom L).obj Y) ≫ (ihom.ev L).app Y) ▷ (ihom Y).obj Z ≫
            MonoidalClosed.comp X Y Z := by
  erw [internalHom_curry_comp (Y := Y) (Z := Z) ((α_ X W ((ihom L).obj Y)).inv ≫
    (f ▷ (ihom L).obj Y) ≫ (ihom.ev L).app Y), ← curry_natural_left]

/-- 内部 Hom の豊穣合成は始域の前合成と可換。 -/
lemma internalHom_comp_pre {X X' : SSet.{u}} (f : X ⟶ X') (Y Z : SSet.{u}) :
    MonoidalClosed.comp X' Y Z ≫ (pre f).app Z =
      (pre f).app Y ▷ _ ≫ MonoidalClosed.comp X Y Z := by
  simpa only [enrichedCategorySelf_hom, enrichedCategorySelf_comp,
    enrichedOrdinaryCategorySelf_eHomWhiskerRight] using
    (eComp_eHomWhiskerRight (V := SSet.{u}) f Y Z)

/-- 前合成とパラメータ付き後合成の交換則。 -/
lemma internalHom_comp_pre_parameter {X X' B Y Z : SSet.{u}} (f : X ⟶ X')
    (t : B ⟶ (ihom Y).obj Z) :
    (pre f).app Y ▷ B ≫ ((ihom X).obj Y) ◁ t ≫ MonoidalClosed.comp X Y Z =
      ((ihom X').obj Y) ◁ t ≫ MonoidalClosed.comp X' Y Z ≫ (pre f).app Z := by
  rw [← whisker_exchange_assoc, ← internalHom_comp_pre]

/-- 全パラメータでの内部 Hom の合成を各重み付き成分へ適用する。 -/
def weightedHomPostSection {W : Iᵒᵖ ⥤ SSet.{u}} {F : I ⥤ SSet.{u}}
    {A B Y Z : SSet.{u}}
    (s : W ⊗ (Functor.const Iᵒᵖ).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y)
    (t : B ⟶ (ihom Y).obj Z) :
    W ⊗ (Functor.const Iᵒᵖ).obj (A ⊗ B) ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Z where
  app i := (α_ (W.obj i) A B).inv ≫ (s.app i ▷ B) ≫
    ((ihom (F.obj i.unop)).obj Y) ◁ t ≫ MonoidalClosed.comp (F.obj i.unop) Y Z
  naturality i j f := by
    change (W.map f ▷ (A ⊗ B)) ≫ (α_ (W.obj j) A B).inv ≫
        (s.app j ▷ B) ≫ ((ihom (F.obj j.unop)).obj Y) ◁ t ≫
          MonoidalClosed.comp (F.obj j.unop) Y Z =
      ((α_ (W.obj i) A B).inv ≫ (s.app i ▷ B) ≫
        ((ihom (F.obj i.unop)).obj Y) ◁ t ≫
          MonoidalClosed.comp (F.obj i.unop) Y Z) ≫ (pre (F.map f.unop)).app Z
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc]
    have hs := s.naturality f
    change (W.map f ▷ A) ≫ s.app j = s.app i ≫ (pre (F.map f.unop)).app Y at hs
    rw [hs, comp_whiskerRight_assoc]
    simp only [Category.assoc]
    apply congrArg (fun k ↦ (α_ (W.obj i) A B).inv ≫ (s.app i ▷ B) ≫ k)
    exact internalHom_comp_pre_parameter (F.map f.unop) t

/-- end の普遍切断と内部 Hom 全体の後合成から、end 上の豊穣な作用を作る。 -/
def weightedHomPostcomposition (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u})
    (Y Z : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y) ⊗ (ihom Y).obj Z ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Z) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (weightedHomPostSection
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y))))
    (𝟙 ((ihom Y).obj Z)))

/-- 豊穣な後合成の各成分は成分の評価と内部 Hom の合成を curry したもの。 -/
lemma weightedHomPostcomposition_π (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u})
    (Y Z : SSet.{u}) (i : Iᵒᵖ) :
    weightedHomPostcomposition W F Y Z ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Z) i =
      curry ((α_ (W.obj i) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y))
        ((ihom Y).obj Z)).inv ≫
        (uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F Y) i) ▷ _) ≫
          MonoidalClosed.comp (F.obj i.unop) Y Z) := by
  rw [weightedHomPostcomposition, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_π]
  dsimp only [weightedHomPostSection, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry]
  erw [Category.id_comp, MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- coend の Hom 比較は内部 Hom 全体の後合成と厳密に可換。 -/
lemma weightedColimitHomComparison_enriched_naturality
    (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y Z : SSet.{u}) :
    MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F) Y Z ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison W F Z =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison W F Y ▷ (ihom Y).obj Z) ≫
        weightedHomPostcomposition W F Y Z := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison_π,
    Category.assoc, weightedHomPostcomposition_π]
  conv_lhs => erw [← curry_natural_left]
  conv_rhs => erw [← curry_natural_left]
  apply congrArg curry
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    ← uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison_π, uncurry_curry]
  exact internalHom_tensorMap_comp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i.unop)

/-- coend の置換射を前合成した Hom 比較も全 Hom パラメータの後合成を保つ。 -/
lemma weightedColimitHomComparison_pre_enriched_naturality
    (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) {K : SSet.{u}}
    (j : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F ⟶ K) (Y Z : SSet.{u}) :
    MonoidalClosed.comp K Y Z ≫ (pre j).app Z ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison W F Z =
      (((pre j).app Y ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison W F Y) ▷ (ihom Y).obj Z) ≫
        weightedHomPostcomposition W F Y Z := by
  rw [← Category.assoc, internalHom_comp_pre, Category.assoc,
    weightedColimitHomComparison_enriched_naturality, comp_whiskerRight_assoc]

/-- coend の恒等射から得られる普遍的な重み付き Hom 切断点。 -/
def weightedColimitUniversalHomPoint (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) :
    𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomDiagram F (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)) :=
  MonoidalClosed.id (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F) ≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison W F (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)

/-- 全 Hom の比較族は、恒等射の普遍切断点と豊穣後合成から厳密に復元できる。 -/
lemma weightedColimitHomComparison_of_universal_point
    (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y : SSet.{u}) :
    (λ_ ((ihom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)).obj Y)).inv ≫
        (weightedColimitUniversalHomPoint W F ▷ (ihom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F)).obj Y) ≫
          weightedHomPostcomposition W F (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F) Y =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison W F Y := by
  rw [weightedColimitUniversalHomPoint, comp_whiskerRight_assoc,
    ← weightedColimitHomComparison_enriched_naturality]
  simp only [← Category.assoc]
  erw [MonoidalClosed.id_comp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F) Y, Category.id_comp]

/-- 置換射の像の普遍切断点も、置換後の全 Hom 比較を後合成で復元する。 -/
lemma weightedColimitHomComparison_pre_of_point
    (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) {K : SSet.{u}}
    (j : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F ⟶ K) (Y : SSet.{u}) :
    (λ_ ((ihom K).obj Y)).inv ≫
        ((curry' j ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison W F K) ▷ (ihom K).obj Y) ≫
          weightedHomPostcomposition W F K Y =
      (pre j).app Y ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitHomComparison W F Y := by
  rw [comp_whiskerRight_assoc, ← weightedColimitHomComparison_enriched_naturality]
  erw [curry'_whiskerRight_comp_assoc (Z := Y) j, Iso.inv_hom_id_assoc]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
