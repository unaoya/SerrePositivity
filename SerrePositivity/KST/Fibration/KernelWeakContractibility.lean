module
public import SerrePositivity.KST.Fibration.RelativeDiagramKernel
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialTerminalWeakContractibility

/-! # 核上の相対図式の弱可縮性

全評価が核に属する場合、相対部分複体は元の図式全体である。
元の図式が零対象を持つなら、その終対象への収縮から弱可縮性が従う。
相対構成の可縮な右上項を構成するための一般補題。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 核に入る全評価を持つ零対象つき図式の相対部分複体は弱可縮。 -/
lemma relativeDiagram_kernel_isWeaklyContractible
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X]
    {J : Type v} (ev : J → (X ⟶ B.obj))
    (he : ∀ j x, (ev j).app (Opposite.op ⦋0⦌) x ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (relativeDiagram q.hom ev : SSet.{u}) := by
  rw [relativeDiagram_eq_top_of_kernel h ev he]
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Subcomplex.topIso X).hom := by
    intro Z _
    let e : (ihom X).obj Z ≅ (ihom ((⊤ : X.Subcomplex) : SSet.{u})).obj Z := {
      hom := (pre (Subcomplex.topIso X).hom).app Z
      inv := (pre (Subcomplex.topIso X).inv).app Z
      hom_inv_id := by
        rw [← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id, pre_id, NatTrans.id_app]
      inv_hom_id := by
        rw [← NatTrans.comp_app, ← pre_map, Iso.hom_inv_id, pre_id, NatTrans.id_app] }
    exact (SSet.π₀Functor.mapIso e).toEquiv.bijective
  have hz : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible X := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).isZero.2.isWeaklyContractible
  have hc := hi.comp hz
  have ht : (Subcomplex.topIso X).hom ≫ terminal.from X =
      terminal.from ((⊤ : X.Subcomplex) : SSet.{u}) := terminal.hom_ext _ _
  rw [ht] at hc
  exact hc

end SerrePositivity.KST.Fibration
