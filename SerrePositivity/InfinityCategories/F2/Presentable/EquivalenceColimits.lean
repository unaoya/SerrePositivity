module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleFunctor
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoconeReversePostcomp
public import SerrePositivity.InfinityCategories.F1B.KanQCatEquivalenceOpposite
public import SerrePositivity.InfinityCategories.Core.ColimitDiagramIso

/-!
概要：同値による元の指定余錐の保存・反映と、小さい κ-filtered 余極限の輸送。
方針：同じ反転錐の既存の極限保存を使い、逆関手と全自然同型で存在を輸送する。
規約：元の全余錐を保持。図式の小ささや濃度の宇宙を変更しない。
使われ方：accessible 圏の同値不変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 同じ元の関手が同値なら、元の任意の全余錐の余極限性を保存・反映する。 -/
lemma equivalence_isColimitCone_iff {K C E : SSet.{u}} [Quasicategory C] [Quasicategory E]
    {G : C ⟶ E} (hG : IsQCatEquivalence G) {D : K ⟶ C} (c : JoinCocone D) :
    IsColimitCone c ↔ IsColimitCone (mapJoinCocone G c) :=
  (F1B.kanIsColimitCone_iff_reverseCone c).trans
    (((F1B.kanIsQCatEquivalence_op hG).isLimitCone_iff (F1B.kanCoconeReverseCone c)).trans
      (isLimitCone_reverse_postcomp_iff c G))

/-- 同値は宇宙 u の元の小さい κ-filtered 全余錐を保存する。 -/
lemma equivalence_preservesSmallKappaFilteredColimits (κ : Cardinal.{u})
    {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E]
    {G : C ⟶ E} (hG : IsQCatEquivalence G) : IsKappaAccessibleFunctor κ G := by
  intro I hI hκ D c hc
  exact (equivalence_isColimitCone_iff hG c).mp hc

/-- 同じ小さい κ-filtered 余極限の存在は、元の同値で輸送される。 -/
lemma hasSmallKappaFilteredColimits_of_equivalence {κ : Cardinal.{u}}
    {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E] (e : QCatEquivalence C E)
    (hC : Ind.HasSmallKappaFilteredColimits κ C) : Ind.HasSmallKappaFilteredColimits κ E := by
  intro I hI hκ D
  obtain ⟨c, hc⟩ := hC I (D ≫ e.inv)
  have he : FunctorIso ((D ≫ e.inv) ≫ e.hom) D := by
    simpa only [Category.assoc, Category.comp_id] using e.invHomIso.precomp D
  exact (hasColimit_iff_of_functorIso he).mp
    ⟨mapJoinCocone e.hom c, (equivalence_isColimitCone_iff e.isQCatEquivalence c).mp hc⟩

end SerrePositivity.InfinityCategories.F2.Presentable
