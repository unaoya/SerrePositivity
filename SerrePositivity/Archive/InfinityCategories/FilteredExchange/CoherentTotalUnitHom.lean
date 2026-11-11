module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpaceLeftHomValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalObject
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Homotopy

/-!
概要：全空間の実際の単位による前合成を、𝒮 内の全左 Hom からの比較として表示する。
方針：左 Hom の値の比較と単位の前合成を続ける。
規約：filtered 性を仮定せず、元の単位を固定する。
使われ方：native 全空間余錐の全 Hom の族と比較する具体的な同値。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}

/-- 概要：全空間の単位による前合成を native な左 Hom から表示する。
方針：左 Hom の内部 Hom 比較の後で、指定単位の前合成を持ち上げる。
規約：元の全空間と元の値を保持。使われ方：余錐の全 Hom 普遍性の比較先。 -/
def coherentTotalUnitHomComparison
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (z : SpaceInfinity.{u} _⦋0⦌) :
    pinchedHomLeft (coherentDiagramTotalVertex F) z ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj
        ((ihom (smallLeftUnstraightening F)).obj (spaceInfinityObject z).obj) :=
  (spaceLeftHomValueEquivalence (coherentDiagramTotalVertex F) z).hom ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      ((pre (coherentDiagramTotalUnit F)).app (spaceInfinityObject z).obj)

/-- 概要：元の全空間の単位から作った全 Hom の比較はホモトピー同値。
方針：値の比較同値と、単位の弱同値による Kan 標的への前合成同値を合成する。
規約：全高次パラメータを含む。使われ方：全 Hom の族の合成整合後の同値性の入力。 -/
lemma coherentTotalUnitHomComparison_homotopyEquivalence
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (z : SpaceInfinity.{u} _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (coherentTotalUnitHomComparison F z) := by
  have h := (spaceLeftHomValueEquivalence (coherentDiagramTotalVertex F) z).isQCatEquivalence
  exact h.isSimplicialHomotopyEquivalence.comp
    (coherentDiagramTotalUnit_pre_homotopyEquivalence F (spaceInfinityObject z).obj).ulift

end SerrePositivity.InfinityCategories.F2
