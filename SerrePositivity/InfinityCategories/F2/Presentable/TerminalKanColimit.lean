module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.Terminal
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaCoconeColimit
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentCoconeTransport

/-!
概要：通常の終対象での左 Kan 値を、元の全図式の native な余極限として回収する。
方針：終対象への Over の忘却同型から局所添字の射影を同型とし、余錐を逆射で制限する。
規約：指定した Kan 値を厳密な頂点として保持する。
使われ方：一点への二つの Kan 拡張の比較から、元の余極限頂点の同型を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 通常の終対象での左 Kan 局所添字は、元の添字と厳密に同型。 -/
lemma leftKanProjection_nerveTerminal_isIso {T : Type u} [Category.{u} T]
    {t : T} (ht : IsTerminal t) {K : SSet.{u}} (p : K ⟶ nerve T) :
    IsIso (leftKanProjection p (nerveVertex t)) := by
  have : IsIso (nerveMap (Over.forget t)) :=
    nerveFunctor.map_isIso (SerrePositivity.InfinityCategories.F1B.overForgetIsoOfTerminal ht).hom
  have he : sliceOverProjection (nervePoint t) =
      (SerrePositivity.InfinityCategories.F1B.nerveOverIso t).inv ≫ nerveMap (Over.forget t) := by
    rw [← SerrePositivity.InfinityCategories.F1B.nerveOverIso_projection, Iso.inv_hom_id_assoc]
  have : IsIso (sliceOverProjection (nervePoint t)) := by rw [he]; infer_instance
  exact inferInstanceAs (IsIso (pullback.fst p (sliceOverProjection (nervePoint t))))

/-- 元の全図式に余極限があれば、終対象での局所 Kan 図式にも余極限がある。 -/
lemma leftKanDiagram_nerveTerminal_hasColimit {T : Type u} [Category.{u} T]
    {t : T} (ht : IsTerminal t) {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ nerve T) (F : K ⟶ X) (hF : HasColimit F) :
    HasColimit (leftKanDiagram p F (nerveVertex t)) := by
  have := leftKanProjection_nerveTerminal_isIso ht p
  exact (hasColimit_iff_restrict_of_precompositionEquivalence F _
    (isPrecompositionEquivalence_of_iso (asIso (leftKanProjection p (nerveVertex t))))).mp hF

/-- 指定された左 Kan 拡張の終対象での値を、元の全図式の余極限の厳密な頂点として得る。 -/
lemma leftKan_nerveTerminal_colimitValue {T : Type u} [Category.{u} T]
    {t : T} (ht : IsTerminal t) {K X : SSet.{u}} [Quasicategory K] [Quasicategory X]
    {p : K ⟶ nerve T} {F : K ⟶ X} {G : nerve T ⟶ X}
    {β : SSet.Homotopy F (p ≫ G)} (hβ : IsLeftKanExtension p F G β) :
    ∃ c : JoinCocone F, IsColimitCone c ∧ c.vertex = G.app _ (nerveVertex t) := by
  obtain ⟨c, hc, hv⟩ := hβ.colimitValue (nerveVertex t)
  let q := leftKanProjection p (nerveVertex t)
  have : IsIso q := leftKanProjection_nerveTerminal_isIso ht p
  have hq := isRightCofinal_of_trivialKanFibration (inv q)
  have hd := (Ind.isColimitCone_iff_restrict_rightCofinal (inv q) hq c).mp hc
  have he : inv q ≫ leftKanDiagram p F (nerveVertex t) = F := by
    dsimp only [leftKanDiagram]
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  refine ⟨HomotopyLimits.coherentCoconeOfDiagramEq he (c.restrict (inv q)),
    (HomotopyLimits.coherentCoconeOfDiagramEq_isColimit_iff he _).mp hd, ?_⟩
  rw [HomotopyLimits.coherentCoconeOfDiagramEq_vertex, JoinCocone.vertex_restrict]
  exact hv

end SerrePositivity.InfinityCategories.F2.Presentable
