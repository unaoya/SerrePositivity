module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedPrismEquivalenceSource

/-!
概要：写像円柱の両端の同値と輸送 prism の厳密な貼り合わせの空間。
方針：終点の同値を円柱の貼り付け射で前合成し、同時端点制限へ引き戻す。
規約：貼り付け射の同値性は要求しない。
使われ方：Kerodon Lemma 5.6.9.1（Tag 02SN）、円柱上の表現と元の表現空間の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：円柱の両端の同値から始点同値と係数 K 上の終点写像を得る射。
方針：終点の同値だけを貼り付け射 f で前合成する。
規約：f は任意の関手でよい。
使われ方：輸送 prism と終点の同値の貼り合わせの底の射。 -/
def pointedCylinderPrismEndpointData {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J)
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceSpace K s ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceSpace J t ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceSpace K s ⊗
        (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection t) :=
  (𝟙 _) ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceι J t ≫ (pre f).app _)

/-- 概要：両端の同値を指定した写像円柱上の全 transport prism の空間。
方針：始点同値に制限した同時端点射を終点の前合成に沿って引き戻す。
規約：終点での貼り合わせは射そのものの一致である。
使われ方：写像円柱の表現の具体的な中間模型。 -/
def pointedCylinderPrismSpace {K J : SSet.{u + 1}} [Quasicategory K] [Quasicategory J]
    (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) : SSet.{u + 1} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismEquivalenceEndpoints K s t) (pointedCylinderPrismEndpointData f s t)

/-- 概要：円柱上の prism の貼り合わせから指定した両端の同値を取り出す。
方針：引き戻しの第二射影。
規約：両端の同値の空間全体への射。
使われ方：境界の表現から円柱上の貼り合わせを選ぶ制限射。 -/
def pointedCylinderPrismEndpoints {K J : SSet.{u + 1}} [Quasicategory K] [Quasicategory J]
    (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderPrismSpace f s t ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceSpace K s ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceSpace J t :=
  pullback.snd _ _

/-- 概要：円柱上の全 prism の両端制限は trivial Kan fibration。
方針：始点同値に制限した同時端点射の全境界持ち上げを底変換する。
規約：f は同値でなくてもよい。
使われ方：境界固定の表現の延長の円柱側の可縮な選択。 -/
lemma pointedCylinderPrismEndpoints_trivialKanFibration {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pointedCylinderPrismEndpoints f s t) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismEquivalenceEndpoints_trivialKanFibration K s t
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _

/-- 概要：指定した両端同値を持つ円柱の全 prism の空間は可縮。
方針：両端制限の trivial Kan fibration の任意の頂点 fiber を取る。
規約：終点との厳密な貼り合わせも含む全高次選択空間。
使われ方：写像円柱と表現空間の比較から境界制限の可縮な fiber を得る。 -/
lemma pointedCylinderPrismFiber_isContractibleKan {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
    (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceSpace K s ⊗
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceSpace J t) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pointedCylinderPrismEndpoints f s t) b) := by
  have := pointedCylinderPrismEndpoints_trivialKanFibration f s t
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
