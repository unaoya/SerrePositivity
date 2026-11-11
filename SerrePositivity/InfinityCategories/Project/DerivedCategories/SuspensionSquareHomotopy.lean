module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberSquareComparisonData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullHomotopyLift

/-! # Semifree 内の suspension 四角形の比較ホモトピー

概要：前合成・後合成から作った四角形の射を Semifree 内の実際のホモトピーに戻す。
方針：周囲の関手圏の射を辺で代表し、全頂点が Semifree であることから円柱全体を持ち上げる。
規約：始点・終点成分の同定は後続。使われ方：D7 の suspension の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial ZeroObject
variable {S : Type u} [CommRing S]

/-- Semifree の標準 suspension 四角形の包含像は明示的な複体四角形。 -/
lemma semifreeSuspensionSquare_inclusion (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).square ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareData X).square :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSquare_inclusion (0 : X.val ⟶ 0) (0 : X.val ⟶ 0)
    X.property (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_zero S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_zero S)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData_square _ _).symm

/-- 包含した四角形を端点とする、周囲の suspension 比較の射。 -/
def suspensionComplexSquareHomOnInclusion {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S} (a : X.val ⟶ Y.val) :
    (SSet.HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).square ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)))) ⟶
        SSet.HomotopyCategory.mk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare Y).square ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenEqToHom (congrArg (fun F => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))
      (semifreeSuspensionSquare_inclusion X)) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareHom a ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenEqToHom (congrArg (fun F => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))
        (semifreeSuspensionSquare_inclusion Y).symm)

/-- 周囲の suspension 比較の射を表す実際の辺。 -/
def suspensionComplexSquareEdge {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S} (a : X.val ⟶ Y.val) :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj
      ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).square ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare Y).square ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ (suspensionComplexSquareHomOnInclusion a))

/-- 選んだ比較辺の類は前合成と後合成から作った射。 -/
lemma suspensionComplexSquareEdge_homMk {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S} (a : X.val ⟶ Y.val) :
    SSet.Truncated.HomotopyCategory.homMk (suspensionComplexSquareEdge a) =
      suspensionComplexSquareHomOnInclusion a :=
  Classical.choose_spec
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ (suspensionComplexSquareHomOnInclusion a))

/-- 全複体の dg nerve における四角形比較の実際のホモトピー代表。 -/
def suspensionComplexSquareHomotopy {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S} (a : X.val ⟶ Y.val) :
    SSet.Homotopy ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).square ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare Y).square ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (suspensionComplexSquareEdge a)

/-- Semifree 内の実際の suspension 四角形比較。 -/
def semifreeSuspensionSquareHomotopy {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S} (a : X.val ⟶ Y.val) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).square (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare Y).square :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.exists_fullInclusion_homotopy S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).square (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare Y).square
    (suspensionComplexSquareHomotopy a))

/-- 持ち上げた suspension 比較の包含像は元の周囲の比較。 -/
lemma semifreeSuspensionSquareHomotopy_inclusion {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S} (a : X.val ⟶ Y.val) :
    (semifreeSuspensionSquareHomotopy a).h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion =
      (suspensionComplexSquareHomotopy a).h :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.exists_fullInclusion_homotopy S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).square (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare Y).square
    (suspensionComplexSquareHomotopy a))

/-- Semifree の suspension 四角形全体のホモトピー圏の射。 -/
def semifreeSuspensionSquareHom {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S} (a : X.val ⟶ Y.val) :
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).square) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S))) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare Y).square) :=
  SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (semifreeSuspensionSquareHomotopy a))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
