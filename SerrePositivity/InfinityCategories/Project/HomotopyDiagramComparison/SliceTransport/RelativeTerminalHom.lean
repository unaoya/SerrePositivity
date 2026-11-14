module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.IntervalFunctorOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundaryCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeTerminalMapping
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceHom

/-!
概要：全パラメータの Hom 全単射と native な相対終点境界充填を接続する。
方針：標準 Hom の式と、相対境界充填の判定を使用する。
規約：元の対象・射・端点の同一視を保持する。使われ方：一般 coherent 極限保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 全始点からの区間写像空間比較が同値なら相対終点である。 -/
lemma relativeTerminal_of_intervalFunctorMap {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (x : X _⦋0⦌)
    (h : ∀ y : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap f y x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeTerminalVertex f x := by
  intro z
  obtain ⟨y, rfl⟩ := SSet.opObjEquiv.symm.surjective z
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedHomMap_equivalence_of_intervalFunctorMap _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalFunctorMap_op_isQCatEquivalence f y x (h y))

/-- 全パラメータの標準 Hom 全単射から相対終点境界充填を得る。 -/
lemma terminalBoundaryLifting_of_parameterHom_bijective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) [InnerFibration f] (x : X _⦋0⦌)
    (h : ∀ (A : SSet.{u}) [Quasicategory A] (y : X _⦋0⦌),
      Function.Bijective (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.constantHomPostcomp f A y x)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting f x := by
  have ht := relativeTerminal_of_intervalFunctorMap f x (fun y ↦
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.intervalFunctorMap_equivalence_of_constantHom_bijective f y x
      (fun A _ ↦ h A y)).isQCatEquivalence)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalBoundaryLifting_of_initialBoundaryLifting_op f x
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanInitialBoundaryLifting_of_relativeInitial (SSet.opFunctor.map f)
      (SSet.opObjEquiv.symm x) ht)

/-- 指定相対終点の境界充填を、同じ反対頂点の相対始点へ移す。 -/
lemma initialBoundaryLifting_op_of_terminal {E B : SSet.{u}} (p : E ⟶ B)
    (x : E _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (SSet.opFunctor.map p) (SSet.opObjEquiv.symm x) := by
  let a : E ≅ E.op.op := (SSet.opFunctorCompOpFunctorIso.app E).symm
  let b : B ≅ B.op.op := (SSet.opFunctorCompOpFunctorIso.app B).symm
  have h := hx.map_iso a b (q := SSet.opFunctor.map (SSet.opFunctor.map p)) (by rfl)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialBoundaryLifting_of_terminalBoundaryLifting_op (SSet.opFunctor.map p)
    (SSet.opObjEquiv.symm x) h

/-- 指定頂点の終点境界充填から写像空間による相対終点性を得る。 -/
lemma relativeTerminal_of_terminalBoundaryLifting {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B)
    (x : E _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p x) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeTerminalVertex p x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeInitialVertex_of_initialBoundary (SSet.opFunctor.map p)
    (SSet.opObjEquiv.symm x) (initialBoundaryLifting_op_of_terminal p x hx)

/-- 終点境界充填は、指定頂点への元の h の Hom 比較を全単射にする。 -/
lemma homMap_bijective_of_terminalBoundaryLifting {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B)
    (x : E _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p x) (y : E _⦋0⦌) :
    Function.Bijective ((hoFunctor.map p).toFunctor.map :
      (HomotopyCategory.mk y ⟶ HomotopyCategory.mk x) →
      (HomotopyCategory.mk (p.app (Opposite.op ⦋0⦌) y) ⟶
        HomotopyCategory.mk (p.app (Opposite.op ⦋0⦌) x))) := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeTerminalVertex_pinchedHomMap_equivalence p x
    (relativeTerminal_of_terminalBoundaryLifting p x hx) y
  have hm : ((hoFunctor.map p).toFunctor.map :
      (HomotopyCategory.mk y ⟶ HomotopyCategory.mk x) → _) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingSpaceHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p y x) := by
    funext α
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingSpaceHomMap_functor p y x α).symm
  rw [hm]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingSpaceHomMap_bijective _ he

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
