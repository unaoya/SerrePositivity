module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorTerminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilyInvariance
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilySquareInverse

/-!
概要：終対象比較を射影した実区間族と、その比較選択によらない全パラメータのホモトピー。
方針：全パラメータの実比較を保持し、終対象性と厳密な fiber の比較を使う。
規約：安定性や有限極限を先取りしない。使われ方：一般安定性判定の実錐比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 終対象への同じ比較を、指定された定値両端を持つ射影後のホモトピーにする。 -/
def terminalComparisonProjectedHomotopy {A E B : SSet.{u}}
    (p : E ⟶ B) (t : E _⦋0⦌) (x : B _⦋0⦌) (f : A ⟶ E)
    (hf : f ≫ p = SSet.const x) (H : SSet.Homotopy f (SSet.const t)) :
    SSet.Homotopy (SSet.const (X := A) x) (SSet.const (p.app (Opposite.op ⦋0⦌) t)) where
  h := H.h ≫ p
  h₀ := by
    rw [← Category.assoc, H.h₀, hf]
    rfl
  h₁ := by
    rw [← Category.assoc, H.h₁, SSet.const_comp]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 終対象への同じ比較を射影した、両端固定の実区間写像空間の族。 -/
def terminalComparisonIntervalFamily {A E B : SSet.{u}}
    (p : E ⟶ B) (t : E _⦋0⦌) (x : B _⦋0⦌) (f : A ⟶ E)
    (hf : f ≫ p = SSet.const x) (H : SSet.Homotopy f (SSet.const t)) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x (p.app (Opposite.op ⦋0⦌) t) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
    (terminalComparisonProjectedHomotopy p t x f hf H))

/-- 同じ実区間族の h Fun の射は、元の比較の後合成を端点輸送したもの。 -/
lemma terminalComparisonIntervalFamily_hom {A E B : SSet.{u}}
    (p : E ⟶ B) (t : E _⦋0⦌) (x : B _⦋0⦌) (f : A ⟶ E)
    (hf : f ≫ p = SSet.const x) (H : SSet.Homotopy f (SSet.const t)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (terminalComparisonIntervalFamily p t x f hf H) =
      eqToHom (congrArg HomotopyCategory.mk (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hf)).symm ≫
        (hoFunctor.map ((ihom A).map p)).toFunctor.map
          (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) ≫
        eqToHom (congrArg HomotopyCategory.mk
          (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const_comp (X := A) t p))) := by
  unfold terminalComparisonIntervalFamily _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge_ofEdge]
  symm
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hf) (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const_comp (X := A) t p))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).map ((truncation 2).map ((ihom A).map p)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (terminalComparisonProjectedHomotopy p t x f hf H))
  change ((ihom A).map p).app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (curry H.h)) =
      SSet.yonedaEquiv (curry (H.h ≫ p))
  rw [← SSet.yonedaEquiv_comp, ← curry_natural_right]

/-- 終対象への任意の二つの比較は、射影後の実区間族としてホモトピック。 -/
lemma terminalComparisonIntervalFamily_homotopy {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) (t : E _⦋0⦌) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex t)
    (x : B _⦋0⦌) (f : A ⟶ E) (hf : f ≫ p = SSet.const x)
    (H H' : SSet.Homotopy f (SSet.const t)) :
    Nonempty (SSet.Homotopy (terminalComparisonIntervalFamily p t x f hf H)
      (terminalComparisonIntervalFamily p t x f hf H')) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_eq_imp_homotopy
  rw [terminalComparisonIntervalFamily_hom, terminalComparisonIntervalFamily_hom]
  have hterm := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise (SSet.const (X := A) t)
    (fun _ ↦ by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant t 0)
      rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero])
  have he : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H') :=
    hterm.isTerminalHo.hom_ext _ _
  rw [he]
/-- 同じ区間族の円柱を展開すると、元の比較の同じ射影を回収する。 -/
lemma terminalComparisonIntervalFamily_h {A E B : SSet.{u}}
    (p : E ⟶ B) (t : E _⦋0⦌) (x : B _⦋0⦌) (f : A ⟶ E)
    (hf : f ≫ p = SSet.const x) (H : SSet.Homotopy f (SSet.const t)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (terminalComparisonIntervalFamily p t x f hf H)).h = H.h ≫ p := by
  rw [terminalComparisonIntervalFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyOfEdge_homotopy]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy,
    Equiv.symm_apply_apply, uncurry_curry, terminalComparisonProjectedHomotopy]
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
