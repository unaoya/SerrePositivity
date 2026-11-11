module
public import SerrePositivity.KST.SConstruction.PerfectDGMoritaEquivalence

/-! # 実 Perf dg 延長の Morita 不変性と全正反復実現
概要：主 Perf 作用の同値を、実 dg nerve の同値と元の全正反復 S 実現へ送る。
方針：全 Hom の擬同型と H⁰ 本質的全射から実同値を選び、完全な逆を保持する。
規約：順方向は元の実 graph 延長。使われ方：K-4d の BF スペクトルへの接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A D E) [(quasiEquivalencePerfectExtension A D E F).IsEquivalence]

/-- 主 Perf 作用の同値は、元の実 dg nerve の同値を与える。 -/
lemma perfectDGMoritaNerve_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension A D E F)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isQCatEquivalence_of_quasiEquivalence (perfectDGExtension A D E F)
    (perfectDGExtension_quasiEquivalence A D E F)

/-- 元の実 Perf dg 延長を順方向に保持する、完全な安定入力の同値。 -/
def perfectDGMoritaStableEquivalence :
    StableModelEquivalence (perfectDGStableModel A D Set.univ)
      (perfectDGStableModel A E Set.univ) := by
  let e := (perfectDGMoritaNerve_isQCatEquivalence A D E F).choose
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.inv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  exact ⟨perfectDGStableMap A D E F,
    ⟨e.inv, preservesCofiberData_of_isExactFunctor e.inv⟩, e.homInvIso, e.invHomIso⟩

/-- 同値の順方向は元の厳密 dg 関手から作った実 Perf 射そのもの。 -/
lemma perfectDGMoritaStableEquivalence_hom :
    (perfectDGMoritaStableEquivalence A D E F).hom = perfectDGStableMap A D E F := rfl

/-- Morita 同値は元の全正有限反復 S 実現を局所化同型へ送る。 -/
lemma perfectDGMoritaRealization_localized_isIso (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (perfectDGStableMap A D E F))) :=
  multiRealization_map_localized_isIso_of_equivalence r
    (perfectDGMoritaStableEquivalence A D E F)

end SerrePositivity.KST.SConstruction
