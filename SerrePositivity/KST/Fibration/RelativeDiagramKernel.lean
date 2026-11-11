module
public import SerrePositivity.KST.Fibration.RelativeDiagramCore

/-! # 核上の相対図式

全ての評価が商で零になる図式では、全ての実辺が成分ごとに W に属する。
従って相対部分複体は図式全体になる。核の図式と相対構成を結ぶための界面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 全頂点を零に送る関手は全ての実辺を可逆に写す。 -/
lemma map_edge_invertible_of_zero {X Y : SSet.{u}} [Quasicategory Y]
    (F : X ⟶ Y) (hF : ∀ x, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x))
    (s : X _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (F.app (Opposite.op ⦋1⦌) s)) := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (f.map ((truncation 2).map F)) :=
    isIso_of_isTerminal (hF _).2.isTerminalHo (hF _).2.isTerminalHo _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := f.map ((truncation 2).map F))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (F.app (Opposite.op ⦋1⦌) s)) rfl).mp hi

/-- 商で全成分が零になる場合、相対部分複体は全図式を保持する。 -/
lemma relativeDiagram_eq_top_of_zero {B C X : SSet.{u}} [Quasicategory C]
    {J : Type v} (q : B ⟶ C) (ev : J → (X ⟶ B))
    (hz : ∀ j x, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((ev j ≫ q).app (Opposite.op ⦋0⦌) x)) :
    relativeDiagram q ev = ⊤ := by
  apply top_unique
  intro n s _ j f
  rw [← NatTrans.naturality_apply]
  exact map_edge_invertible_of_zero (ev j ≫ q) (hz j) (X.map f.op s)

/-- 包含の本質像に全評価が属する図式では、相対条件は自動的に成立する。 -/
lemma relativeDiagram_eq_top_of_kernel
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) {X : SSet.{u}} {J : Type v}
    (ev : J → (X ⟶ B.obj))
    (he : ∀ j x, (ev j).app (Opposite.op ⦋0⦌) x ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) :
    relativeDiagram q.hom ev = ⊤ :=
  relativeDiagram_eq_top_of_zero q.hom ev (fun j x => (h.kernel _).2 (he j x))

end SerrePositivity.KST.Fibration
