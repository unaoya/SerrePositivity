module

public import SerrePositivity.KST.Spectra.PointedWeightedEndBasepoint
public import SerrePositivity.KST.Spectra.PointedWeightedConeCompatibility
public import SerrePositivity.KST.Spectra.PointedVertexComparison

/-!
概要：点つき end への錐の標準比較と通常の単体集合の比較の一致。
方針：自由基点からの定数族を元の成分へ制限し、end の各射影で比較する。
規約：極限錐の仮定も Kan 性も不要。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。自明作用の標準射の具体式。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet


namespace SerrePositivity.KST.Spectra.PointedWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma unit_inverse_restrict (Y : PointedSimplicialSet.{u}) :
    (unitIsoSelf (X := Y)).inv.right ≫
        FreePointedHomRestriction.restrict (𝟙_ SSet.{u}) Y =
      curry (snd (𝟙_ SSet.{u}) Y.right) := by
  rw [FreePointedHomRestriction.restrict, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.unit_inv_eq_curry, PointedMapping.curry_eq_smashCurry]
  erw [PointedObject.smashCurry_ι]
  rw [curry_pre_app]
  congr 1
  change coprod.inl ▷ Y.right ≫
      (PointedObject.smashQuotient (𝟙_ PointedSimplicialSet.{u}) Y).right ≫
        (λ_ Y).hom.right = snd (𝟙_ SSet.{u}) Y.right
  erw [← Under.comp_right, PointedObject.smashQuotient_leftUnitHom]
  exact PointedObject.leftUnitRaw_first Y

/-- 概要：点つき定数族を元の源に制限すると通常の定数族になる。
方針：重みを単位へ潰す射の制限の自然性と単位の評価を使う。
規約：通常の単体集合の射の等式。
使われ方：Goerss–Jardine VIII §2。自明作用の標準射の模型の比較。 -/
lemma constantFamily_restrict (A : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    (constantFamily A Y).right ≫ FreePointedHomRestriction.restrict A Y =
      curry (snd A Y.right) := by
  rw [constantFamily, Under.comp_right, Category.assoc]
  change (unitIsoSelf (X := Y)).inv.right ≫
      ((pre (PointedObject.adjoinFunctor.map (toUnit A))).app Y).right ≫
        FreePointedHomRestriction.restrict A Y = _
  rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre,
    FreePointedHomRestriction.natural_pre, ← Category.assoc,
    unit_inverse_restrict, curry_pre_app, whiskerRight_snd]

/-- 概要：点つき錐の比較射を忘却すると通常の錐の比較射。
方針：end の各射影で定数族の制限と curry の自然性を照合する。
規約：重みは任意、係数は点つき単体集合。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。標準射の基礎 end での式。 -/
lemma underlyingIso_coneComparison {I : Type u} [SmallCategory I]
    (W : I ⥤ SSet.{u}) {D : I ⥤ PointedSimplicialSet.{u}} (c : Cone D) :
    (coneComparison W c).right ≫ (underlyingIso W D).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W (PointedSimplicialSet.forget.mapCone c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [Category.assoc, underlyingIso_π, ← Category.assoc, ← Under.comp_right,
    coneComparison_π, Under.comp_right, Category.assoc, constantFamily_restrict,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π, ← curry_natural_left]
  congr 1

end

end SerrePositivity.KST.Spectra.PointedWeightedEnd
