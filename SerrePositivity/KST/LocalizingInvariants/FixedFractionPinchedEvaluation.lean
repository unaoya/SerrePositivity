module

public import SerrePositivity.KST.LocalizingInvariants.FixedFractionEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightIntervalHomotopySection

/-!
概要：両端固定の分数評価を元の右 pinched 写像空間へ移す。
方針：既存の区間比較のホモトピー切断を、構成済みの実評価族へ適用する。
規約：元の区間評価との実単体的ホモトピーを保持。同値性の証明は後続。
使われ方：pinchedHomMap による矢印局所化比較の充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q) (W : Set (X _⦋1⦌))
  (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) (x y : X _⦋0⦌)

def fixedFractionPinchedEvaluation : fixedMarkedSpans X W x y ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_exists_homotopy
    (fixedFractionEvaluation F W hF x y))

def fixedFractionPinchedComparisonHomotopy : SSet.Homotopy
    (fixedFractionPinchedEvaluation F W hF x y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y))
    (fixedFractionEvaluation F W hF x y) :=
  Classical.choice (Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_exists_homotopy
    (fixedFractionEvaluation F W hF x y)))

end SerrePositivity.KST.LocalizingInvariants
