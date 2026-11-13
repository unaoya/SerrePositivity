module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.HomotopyEvaluationClass

/-! # 関手の h の射の頂点評価

概要：関手 ∞ 圏の h の射を自然変換にした成分は、頂点評価で写した射に等しい。
方針：辺の代表を取り、h の積比較の定義と頂点の定値辺を照合する。
規約：端点の表示を Arrow に含める。使われ方：完全関手の懸垂比較の成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：関手の h の射に対応する自然変換の成分は頂点評価の像。
方針：射を辺の類で表し、積の恒等辺を定値辺に戻す。
規約：値域 Y の quasicategory 性のみ。使われ方：可逆二胞体の成分の計算。 -/
lemma functorHomotopyEvaluation_map_app_arrow {A Y : SSet.{u}} [Quasicategory Y]
    {v w : ((ihom A).obj Y) _⦋0⦌}
    (f : (SSet.HomotopyCategory.mk v : hoFunctor.obj ((ihom A).obj Y)) ⟶
      SSet.HomotopyCategory.mk w) (x : A _⦋0⦌) :
    Arrow.mk (((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation A Y).map f).app (SSet.HomotopyCategory.mk x)) =
      Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) x)).toFunctor.map f) := by
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective v w f
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  change e.edge.app (Opposite.op ⦋1⦌) (𝟙 (Opposite.op ⦋1⦌))
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).edge) =
    e.edge.app (Opposite.op ⦋1⦌) (𝟙 (Opposite.op ⦋1⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]

/-- 概要：可逆二胞体の通常の自然同型の成分も頂点評価で計算できる。
方針：自然同型への変換の端点輸送を消して射の評価式を使う。
規約：頂点表示の違いを Arrow に含める。使われ方：懸垂比較の始点と終点。 -/
lemma functorIso_toNatIso_hom_app_arrow {A Y : SSet.{u}} [Quasicategory Y]
    {f g : A ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (x : A _⦋0⦌) :
    Arrow.mk (e.toNatIso.hom.app (SSet.HomotopyCategory.mk x)) =
      Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) x)).toFunctor.map e.hom) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.toNatIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    eqToIso.inv, NatTrans.comp_app, eqToHom_app, eqToHom_refl,
    Category.id_comp, Category.comp_id, Functor.mapIso_hom]
  change Arrow.mk (((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation A Y).map e.hom).app
    (SSet.HomotopyCategory.mk x)) = _
  exact functorHomotopyEvaluation_map_app_arrow e.hom x

/-- 概要：関手の h の射の成分を後合成すると、後合成した射の成分になる。
方針：辺の代表で積の評価と後合成を計算する。
規約：始域側の値域 E は quasicategory。使われ方：自然同型の後合成の成分。 -/
lemma functorHomotopyEvaluation_postcomp_map_app {A E B : SSet.{u}} [Quasicategory E]
    (q : E ⟶ B) {v w : ((ihom A).obj E) _⦋0⦌}
    (a : (SSet.HomotopyCategory.mk v : hoFunctor.obj ((ihom A).obj E)) ⟶
      SSet.HomotopyCategory.mk w) (x : A _⦋0⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation A B).map
      ((hoFunctor.map ((ihom A).map q)).toFunctor.map a)).app (SSet.HomotopyCategory.mk x) =
    (hoFunctor.map q).toFunctor.map
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation A E).map a).app (SSet.HomotopyCategory.mk x)) := by
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective v w a
  rfl

/-- 概要：可逆二胞体を後合成してから自然同型にする操作は成分の後合成と一致する。
方針：端点輸送を消し、h の射の後合成の評価を使う。
規約：E の quasicategory 性のみ。使われ方：懸垂比較と角の評価の可換性。 -/
lemma functorIso_toNatIso_postcomp_hom_app {A E B : SSet.{u}} [Quasicategory E]
    {f g : A ⟶ E} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (q : E ⟶ B) (x : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e q).toNatIso.hom.app (SSet.HomotopyCategory.mk x) =
      (hoFunctor.map q).toFunctor.map (e.toNatIso.hom.app (SSet.HomotopyCategory.mk x)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.toNatIso, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom, eqToIso.inv, NatTrans.comp_app, eqToHom_app, eqToHom_refl,
    Category.id_comp, Category.comp_id, Functor.mapIso_hom]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation A B).map
      ((hoFunctor.map ((ihom A).map q)).toFunctor.map e.hom)).app
      (SSet.HomotopyCategory.mk x) =
    (hoFunctor.map q).toFunctor.map
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation A E).map e.hom).app (SSet.HomotopyCategory.mk x))
  exact functorHomotopyEvaluation_postcomp_map_app q e.hom x

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
