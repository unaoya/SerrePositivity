module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaCoconeColimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentCoconeTransport

/-!
概要：通常の終対象での左 Kan 値を、元の全図式の native な余極限として回収する。
方針：終対象への Over の忘却同型から局所添字の射影を同型とし、余錐を逆射で制限する。
規約：指定した Kan 値を厳密な頂点として保持する。
使われ方：一点への二つの Kan 拡張の比較から、元の余極限頂点の同型を得る。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 通常の終対象での左 Kan 局所添字は、元の添字と厳密に同型。 -/
lemma leftKanProjection_nerveTerminal_isIso {T : Type u} [Category.{u} T]
    {t : T} (ht : IsTerminal t) {K : SSet.{u}} (p : K ⟶ nerve T) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex t)) := by
  have : IsIso (nerveMap (Over.forget t)) :=
    nerveFunctor.map_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.overForgetIsoOfTerminal ht).hom
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint t) =
      (_root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso t).inv ≫ nerveMap (Over.forget t) := by
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.Section1_2_9.nerveOverIso_projection, Iso.inv_hom_id_assoc]
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint t)) := by rw [he]; infer_instance
  exact inferInstanceAs (IsIso (pullback.fst p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint t))))

/-- 元の全図式に余極限があれば、終対象での局所 Kan 図式にも余極限がある。 -/
lemma leftKanDiagram_nerveTerminal_hasColimit {T : Type u} [Category.{u} T]
    {t : T} (ht : IsTerminal t) {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ nerve T) (F : K ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram p F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex t)) := by
  have := leftKanProjection_nerveTerminal_isIso ht p
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_restrict_of_precompositionEquivalence F _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex t))))).mp hF

/-- 指定された左 Kan 拡張の終対象での値を、元の全図式の余極限の厳密な頂点として得る。 -/
lemma leftKan_nerveTerminal_colimitValue {T : Type u} [Category.{u} T]
    {t : T} (ht : IsTerminal t) {K X : SSet.{u}} [Quasicategory K] [Quasicategory X]
    {p : K ⟶ nerve T} {F : K ⟶ X} {G : nerve T ⟶ X}
    {β : SSet.Homotopy F (p ≫ G)} (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension p F G β) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ∧ c.vertex = G.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex t) := by
  obtain ⟨c, hc, hv⟩ := hβ.colimitValue (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex t)
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex t)
  have : IsIso q := leftKanProjection_nerveTerminal_isIso ht p
  have hq := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_trivialKanFibration (inv q)
  have hd := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal (inv q) hq c).mp hc
  have he : inv q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram p F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex t) = F := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram]
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq he (c.restrict (inv q)),
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff he _).mp hd, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict]
  exact hv

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
