module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorCompositionLaws
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
概要：小さい Kan 対象を終対象上の left fibration として表し、相対 Hom を元の内部 Hom と同定する。
方針：終対象への全射が一意であるため、全関手は自動的に底を保つ。
規約：元の Kan 対象の全単体と全パラメーターの関手を保持し、同値でなく厳密な同型を与える。
使われ方：相対豊穣 Hom と、空間の全内部 Hom 関手との比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 小さい Kan 対象の元の終対象射は、全ての左ホーンの持ち上げを持つ。 -/
lemma kanTerminal_leftFibration (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (terminal.from K.obj) := by
  constructor
  intro A D j hj
  cases hj with
  | @intro n i hi =>
    constructor
    intro a b sq
    obtain ⟨g, hg⟩ := KanComplex.hornFilling a
    exact CommSq.HasLift.mk' {
      l := g
      fac_left := hg.symm
      fac_right := terminal.hom_ext _ _ }

/-- 元の Kan 対象を、同じ全空間を持つ終対象上の left fibration に束縛する。 -/
def kanTerminalObject (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject (⊤_ SSet.{u}) :=
  ⟨Over.mk (terminal.from K.obj), kanTerminal_leftFibration K⟩

/-- 内部 Hom の終対象への射は、元の唯一の定値図式を表す。 -/
lemma ihom_terminal_map_const (A E : SSet.{u}) :
    (ihom A).map (terminal.from E) =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (terminal.from A)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro F
  apply Functor.HomObj.ext
  funext m α
  apply ConcreteCategory.hom_ext
  intro a
  have hm : IsTerminal ((⊤_ SSet.{u}).obj m) :=
    IsTerminal.isTerminalObj ((evaluation SimplexCategoryᵒᵖ (Type u)).obj m)
      (⊤_ SSet.{u}) terminalIsTerminal
  let : Unique ((⊤_ SSet.{u}).obj m) := Types.isTerminalEquivUnique _ hm
  exact Subsingleton.elim _ _

/-- 終対象上の相対 Hom は、元の同じ全内部 Hom と厳密に同型。 -/
def terminalRelativeHomIso (A E : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (terminal.from E) (terminal.from A) ≅ (ihom A).obj E where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map (terminal.from E)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (terminal.from A))
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (𝟙 _) (by
    rw [Category.id_comp, ihom_terminal_map_const])
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.comp_id, Category.id_comp]
  inv_hom_id := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

/-- 逆同型は、元の内部 Hom へ含めると恒等射を回収する。 -/
lemma terminalRelativeHomIso_inv_ι (A E : SSet.{u}) :
    (terminalRelativeHomIso A E).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map (terminal.from E)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (terminal.from A)) = 𝟙 _ :=
  (terminalRelativeHomIso A E).inv_hom_id

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
