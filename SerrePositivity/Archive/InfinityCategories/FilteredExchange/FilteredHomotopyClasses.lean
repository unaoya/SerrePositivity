module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FilteredHomotopyFactorization
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：Kan 値の filtered 図式における有限写像のホモトピー類の一致は後続段で検出できる。
方針：余極限の Kan 性、成分とホモトピーの比較、有限円柱の相対因子分解を合成する。
規約：通常の小圏による strict 図式についての主張。
使われ方：coherent な filtered 余極限との比較と compact 性の準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：有限形状からの二射の余極限でのホモトピー類の一致は一つの後続段で成立する。
方針：実際のホモトピーへ移し、両端を固定した有限円柱の因子分解を使う。
規約：元の段 j とそこからの後続射を保持する。使われ方：有限な写像の同一視の検出。 -/
lemma piZero_eq_iff_exists_homotopy_at_stage
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ SSet.{u}} [∀ i, KanComplex (F.obj i)]
    {c : Cocone F} (hc : IsColimit c) {K : SSet.{u}} [K.Finite]
    (j : I) (f g : K ⟶ F.obj j) :
    SSet.π₀.mk (functorVertex (f ≫ c.ι.app j)) =
      SSet.π₀.mk (functorVertex (g ≫ c.ι.app j)) ↔
        ∃ (k : I) (v : j ⟶ k), Nonempty (SSet.Homotopy (f ≫ F.map v) (g ≫ F.map v)) := by
  have := kanComplex_of_filtered_isColimit hc
  have (i : I) : KanComplex (((Functor.const I).obj c.pt).obj i) :=
    kanComplex_of_filtered_isColimit hc
  constructor
  · intro h
    obtain ⟨H⟩ := (functorVertex_piZero_eq_iff_homotopy _ _).1 h
    exact exists_homotopy_at_stage_of_filtered_isColimit hc j f g H
  · rintro ⟨k, v, ⟨H⟩⟩
    apply (functorVertex_piZero_eq_iff_homotopy _ _).2
    have H' := functorHomotopyPostcomp H (c.ι.app k)
    simpa only [Category.assoc, c.w v] using! (show Nonempty (SSet.Homotopy
      ((f ≫ F.map v) ≫ c.ι.app k) ((g ≫ F.map v) ≫ c.ι.app k)) from ⟨H'⟩)

end SerrePositivity.InfinityCategories.F2
