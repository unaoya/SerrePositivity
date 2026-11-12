module

public import SerrePositivity.KST.Spectra.TotalizationBousfieldKanComparison
public import SerrePositivity.KST.Spectra.PointedHomotopyLimit
public import SerrePositivity.KST.Spectra.PointedWeightedEndBasepoint

/-!
概要：通常の点つき Tot から段ごとの Bousfield–Kan end への比較。
方針：終頂点による比較射が基点の定数族を保つことを射影ごとに検証する。
規約：弱同値性や ∞ 極限性はこの構成に含めない。
使われ方：Goerss–Jardine VIII §1。Sp-4 の比較の点つき模型。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet

open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.PointedTotalization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 通常の Tot の標準基点は Bousfield–Kan end の標準基点へ送られる。 -/
lemma bousfieldKanComparison_basepoint (X : CosimplicialObject PointedSimplicialSet.{u}) :
    (obj X).hom ≫ CosimplicialTotalization.bousfieldKanComparison
      (X ⋙ PointedSimplicialSet.forget) =
    (PointedHomotopyLimit.obj (AsSmall.down ⋙ X)).hom := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro j
  rw [Category.assoc, CosimplicialTotalization.bousfieldKanComparison_π,
    ← Category.assoc]
  change (CosimplicialTotalization.lift (basepointFamily X) ≫
    CosimplicialTotalization.π (X ⋙ PointedSimplicialSet.forget) (AsSmall.down.obj j)) ≫ _ = _
  rw [CosimplicialTotalization.lift_π]
  change curry (snd _ _ ≫ (X.obj (AsSmall.down.obj j)).hom) ≫ _ =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison _ (PointedHomotopyLimit.basepointCone (AsSmall.down ⋙ X)) ≫ _
  erw [curry_pre_app]
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π]
  rw [← Category.assoc, whiskerRight_snd]
  rfl

/-- 通常の点つき Tot から Bousfield–Kan end への実際の点つき射。 -/
def bousfieldKanComparison (X : CosimplicialObject PointedSimplicialSet.{u}) :
    obj X ⟶ PointedHomotopyLimit.obj (AsSmall.down ⋙ X) :=
  Under.homMk (CosimplicialTotalization.bousfieldKanComparison
    (X ⋙ PointedSimplicialSet.forget)) (bousfieldKanComparison_basepoint X)

/-- 点つき比較射は係数の自然変換と厳密に可換。 -/
lemma bousfieldKanComparison_naturality {X Y : CosimplicialObject PointedSimplicialSet.{u}}
    (f : X ⟶ Y) :
    map f ≫ bousfieldKanComparison Y = bousfieldKanComparison X ≫
      PointedHomotopyLimit.map (Functor.whiskerLeft AsSmall.down f) := by
  apply Under.UnderMorphism.ext
  exact CosimplicialTotalization.bousfieldKanComparison_naturality
    (Functor.whiskerRight f PointedSimplicialSet.forget)

/-- BF の段で用いる点つき enriched end への同じ比較射。 -/
def weightedEndComparison (X : CosimplicialObject PointedSimplicialSet.{u}) :
    obj X ⟶ PointedWeightedEnd.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _) (AsSmall.down ⋙ X) :=
  Under.homMk ((bousfieldKanComparison X).right ≫
    (PointedWeightedEnd.underlyingIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _) (AsSmall.down ⋙ X)).inv) (by
      apply (cancel_mono (PointedWeightedEnd.underlyingIso
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _) (AsSmall.down ⋙ X)).hom).mp
      rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        PointedWeightedEnd.underlyingIso_basepoint]
      exact bousfieldKanComparison_basepoint X)

/-- enriched end へ移した比較を忘却すると元の比較射に戻る。 -/
@[reassoc]
lemma weightedEndComparison_underlying (X : CosimplicialObject PointedSimplicialSet.{u}) :
    (weightedEndComparison X).right ≫
      (PointedWeightedEnd.underlyingIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _) (AsSmall.down ⋙ X)).hom =
    (bousfieldKanComparison X).right := by
  change (_ ≫ _) ≫ _ = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- enriched end への比較も係数の射に自然。 -/
lemma weightedEndComparison_naturality {X Y : CosimplicialObject PointedSimplicialSet.{u}}
    (f : X ⟶ Y) :
    map f ≫ weightedEndComparison Y = weightedEndComparison X ≫
      PointedWeightedEnd.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _) (Functor.whiskerLeft AsSmall.down f) := by
  apply Under.UnderMorphism.ext
  apply (cancel_mono (PointedWeightedEnd.underlyingIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _) (AsSmall.down ⋙ Y)).hom).mp
  change ((map f).right ≫ (weightedEndComparison Y).right) ≫ _ =
    ((weightedEndComparison X).right ≫
      (PointedWeightedEnd.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _)
        (Functor.whiskerLeft AsSmall.down f)).right) ≫ _
  rw [Category.assoc, weightedEndComparison_underlying, Category.assoc,
    PointedWeightedEnd.underlyingIso_natural, ← Category.assoc,
    weightedEndComparison_underlying]
  exact congrArg Under.Hom.right (bousfieldKanComparison_naturality f)

end
end SerrePositivity.KST.Spectra.PointedTotalization
