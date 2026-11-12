module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorRelativeTerminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeTerminalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FiberwiseHomotopy
/-!
概要：相対終対象の切断による全パラメータの底を固定した比較。
方針：元の相対境界充填と right fibration の表現を実射へ接続する。
規約：安定性や有限余極限を仮定しない。使われ方：HA 1.4.2.27 の余錐比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
lemma relativeTerminalFamilyComparison_exists {K E B : SSet.{u}} (p : E ⟶ B)
    (f g : K ⟶ E) (hfg : f ≫ p = g ≫ p)
    (ht : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p (g.app (Opposite.op ⦋0⦌) k)) :
    ∃ e : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj E))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g),
      (e.map ((truncation 2).map ((ihom K).map p))).edge =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ p)) 1 := by
  let q := (ihom K).map p
  let fp := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ p)
  let x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q fp) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    rfl⟩
  let y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q fp) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ p) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ p)
    rw [hfg]⟩
  have hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex y := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting.isTerminalVertex_fiber q fp y
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalBoundaryLifting_ihom_of_pointwise p g ht)
  obtain ⟨e⟩ := hy.nonempty_edge x
  exact ⟨e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q fp)), e.edge.property⟩
lemma relativeTerminalFamilyHomotopy_exists {K E B : SSet.{u}} (p : E ⟶ B)
    (f g : K ⟶ E) (hfg : f ≫ p = g ≫ p)
    (ht : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p (g.app (Opposite.op ⦋0⦌) k)) :
    ∃ H : SSet.Homotopy f g,
      H.h ≫ p = CartesianMonoidalCategory.fst K (Δ[1] : SSet.{u}) ≫ f ≫ p := by
  obtain ⟨e, he⟩ := relativeTerminalFamilyComparison_exists p f g hfg ht
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.simplicialHomotopyOfFunctorEdge_comp_eq_constant p (f ≫ p) e he⟩
lemma relativeTerminalSectionComparison_exists {E B : SSet.{u}} (p : E ⟶ B)
    (r : B ⟶ E) (hr : r ≫ p = 𝟙 B)
    (ht : ∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p (r.app (Opposite.op ⦋0⦌) b)) :
    ∃ e : Truncated.Edge (X := (truncation 2).obj ((ihom E).obj E))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 E)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (p ≫ r)),
      (e.map ((truncation 2).map ((ihom E).map p))).edge =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) 1 := by
  simpa only [Category.id_comp] using
    relativeTerminalFamilyComparison_exists p (𝟙 E) (p ≫ r)
      (by rw [Category.id_comp, Category.assoc, hr, Category.comp_id])
      (fun a ↦ ht (p.app _ a))
lemma relativeTerminalSectionHomotopy_exists {E B : SSet.{u}} (p : E ⟶ B)
    (r : B ⟶ E) (hr : r ≫ p = 𝟙 B)
    (ht : ∀ b : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p (r.app (Opposite.op ⦋0⦌) b)) :
    ∃ H : SSet.Homotopy (𝟙 E) (p ≫ r),
      H.h ≫ p = CartesianMonoidalCategory.fst E (Δ[1] : SSet.{u}) ≫ p := by
  obtain ⟨e, he⟩ := relativeTerminalSectionComparison_exists p r hr ht
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.simplicialHomotopyOfFunctorEdge_comp_eq_constant p p e he⟩
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
