module

public import SerrePositivity.KST.Spectra.PartialTotalizationTower
public import SerrePositivity.KST.Spectra.SkeletalWeightedEndLimit
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FibrationTowerLimitCone
public import SerrePositivity.KST.Spectra.TowerHomotopyComparison

/-!
概要：通常 Tot は有限骨格の塔の具体的な整合族の極限と基点を保って同型。
方針：骨格の重みの余極限、忘却の極限保存、具体的な塔の極限錐を比較する。
規約：同型の座標は通常 Tot から骨格への実際の制限射。
使われ方：Goerss–Jardine VIII §1。Milnor 完全性を通常 Tot へ戻す界面。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet Opposite
namespace SerrePositivity.KST.Spectra.PartialTotalizationTower
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 標準単体 end と具体的な骨格の塔の極限の同型。 -/
def endLimitIso (X : CosimplicialObject PointedSimplicialSet.{u}) :
    (PointedWeightedEnd.obj (AsSmall.down ⋙ stdSimplex) (AsSmall.down ⋙ X)).right ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (stage X n).right) (fun n ↦ (step X n).right) :=
  (isLimitOfPreserves PointedSimplicialSet.forget
    (SkeletalWeightedEnd.coneIsLimit (AsSmall.down ⋙ stdSimplex)
      (AsSmall.down ⋙ X))).conePointUniqueUpToIso
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.sequentialConeIsLimit (diagram X ⋙ PointedSimplicialSet.forget))

@[reassoc]
lemma endLimitIso_hom_projection (X : CosimplicialObject PointedSimplicialSet.{u}) (n : ℕ) :
    (endLimitIso X).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection
      (fun n ↦ (stage X n).right) (fun n ↦ (step X n).right) n =
    ((SkeletalWeightedEnd.cone (AsSmall.down ⋙ stdSimplex)
      (AsSmall.down ⋙ X)).π.app (op n)).right :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

/-- 通常 Tot と、骨格の塔の具体的な整合族の極限との同型。 -/
def limitIso (X : CosimplicialObject PointedSimplicialSet.{u}) :
    (PointedTotalization.obj X).right ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (stage X n).right) (fun n ↦ (step X n).right) :=
  PointedSimplicialSet.forget.mapIso (PointedTotalization.standardEndIso X) ≪≫ endLimitIso X

/-- 同型の各座標は通常 Tot から元の骨格への制限。 -/
@[reassoc]
lemma limitIso_hom_projection (X : CosimplicialObject PointedSimplicialSet.{u}) (n : ℕ) :
    (limitIso X).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection
      (fun n ↦ (stage X n).right) (fun n ↦ (step X n).right) n = (restriction X n).right := by
  change ((PointedTotalization.standardEndIso X).hom.right ≫ (endLimitIso X).hom) ≫ _ = _
  rw [Category.assoc, endLimitIso_hom_projection]
  rfl

/-- 同型は通常 Tot の標準基点を骨格の塔の基点の整合族へ送る。 -/
lemma limitIso_basepoint (X : CosimplicialObject PointedSimplicialSet.{u}) :
    (limitIso X).hom.app _ (PointedTotalization.obj X).basepoint =
      PointedFibrationTower.limitBasepoint (stage X) (step X) := by
  apply Subtype.ext
  funext n
  have he := congrArg
    (fun f : (PointedTotalization.obj X).right ⟶ (stage X n).right ↦
      f.app _ (PointedTotalization.obj X).basepoint) (limitIso_hom_projection X n)
  exact he.trans (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (restriction X n))

end
end SerrePositivity.KST.Spectra.PartialTotalizationTower
