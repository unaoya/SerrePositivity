module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.ClassifiedConeLift
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationConeLimit

/-!
概要：元の前層が極限へ送る底の極限錐を、小さい全空間自身の極限錐へ持ち上げる。
方針：同じ指定図式を固定した全延長空間の可縮性と相対境界充填を使う。
規約：図式と全錐の射影を厳密に保持し、底の極限存在は明示する。
使われ方：有限積保存する前層の元の圏の有限積の存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open _root_.CategoryTheory _root_.SSet
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HA.Section5_2_2

/-- 元の底の極限錐をその像も極限となるよう持ち上げれば、同じ全錐は全空間でも極限。 -/
lemma classifiedCone_isLimit
    {K B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    {d : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone d)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) a))
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) a)))) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.isLimitCone_of_leftFibration_extension (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) a ha
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.classifiedConeExtension_isContractibleKan
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) a) F hF d rfl)

/-- 元の図式と底の同じ極限錐を厳密に保つ、全空間内の極限錐が存在する。 -/
lemma exists_classifiedLimitCone
    {K B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (d : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c))) :
    ∃ a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone d, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone a ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) a = c := by
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_classifiedConeLift c F hF d rfl
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F) a = c := Subtype.ext ha
  refine ⟨a, ?_, he⟩
  apply _root_.SerrePositivity.InfinityCategories.HA.Section5_2_2.classifiedCone_isLimit F a
  · rwa [he]
  · rwa [he]

/-- 有限積保存する元の前層の全空間には、底に存在する同じ有限積の持ち上げが存在。 -/
lemma hasLimit_smallLeftUnstraightening_of_finiteProducts
    {B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hF : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PreservesFiniteProductsFromSmallSource F)
    {J : Type u} [Finite J] (d : nerve (Discrete J) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection F)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit d := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨a, ha, _⟩ := _root_.SerrePositivity.InfinityCategories.HA.Section5_2_2.exists_classifiedLimitCone F d c hc (hF.map_isLimit hc)
  exact ⟨a, ha⟩

end SerrePositivity.InfinityCategories.HA.Section5_2_2

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "5.2.2.39" (partial := direction) "仮定：準圏 B、空間値 F:B→S と指定した小さい left unstraightening、底の極限錐と F による像の極限性（Lean が強い：この選択した分類模型と底で極限となる場合）。結論：任意の持ち上げた始域図式に、底の同じ錐を厳密に保つ全空間の極限錐が存在する。反対を取ると HA の right fibration の (2)⇒(3) の向きに一致する。一般の f への比較と (1)・(2) の同値の逆向きは含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.Section5_2_2.classifiedCone_isLimit
attribute [cite HA "5.2.2.39" (partial := direction) "仮定：準圏 B、空間値 F:B→S と指定した小さい left unstraightening、底の極限錐と F による像の極限性（Lean が強い：この選択した分類模型と底で極限となる場合）。結論：任意の持ち上げた始域図式に、底の同じ錐を厳密に保つ全空間の極限錐が存在する。反対を取ると HA の right fibration の (2)⇒(3) の向きに一致する。一般の f への比較と (1)・(2) の同値の逆向きは含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.Section5_2_2.exists_classifiedLimitCone
