module
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.Reindexing.ConstantRestrictionArrow
/-!
概要：全源比較の前合成と等式による端点輸送を、評価後の全 Arrow で比較する。
方針：既存の前合成評価公式と同じ関手等式の消去を使う。
規約：元の全関手射と指定点を保持する。
使われ方：実忘却の全源同型を元の置換成分辺へ回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open CategoryTheory SSet MonoidalClosed _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 概要：全関手同型の前合成の評価は元の同じ像の点での評価。
方針：既存の全関手射の前合成評価を使う。
規約：同じ順射を全 Arrow で保持。使われ方：自由・置換源の頂点表示の回収。 -/
lemma functorIsoEvaluate_precomp_arrow {K L X : SSet.{u}} {F G : L ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) (q : K ⟶ L) (x : K.obj (Opposite.op ⦋0⦌)) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (e.precomp q).hom x) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate e.hom (q.app (Opposite.op ⦋0⦌) x)) := by
  change Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (U := q ≫ F) (V := q ≫ G)
    ((hoFunctor.map ((pre q).app X)).toFunctor.map e.hom) x) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_precomp]

/-- 概要：同じ関手等式の評価は指定した点での同じ頂点等式輸送。
方針：元の関手等式を消去して評価の恒等則を使う。
規約：元の点と端点等式を保持。使われ方：全源同型の等式輸送の除去。 -/
lemma functorIsoEvaluate_eqToIso_hom {L X : SSet.{u}} {F G : L ⟶ X}
    (h : F = G) (x : L.obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (U := F) (V := G)
      (eqToIso (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) h)).hom x =
      eqToHom (congrArg HomotopyCategory.mk
        (congrArg (fun f : L ⟶ X => f.app (Opposite.op ⦋0⦌) x) h)) := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_id, eqToHom_refl]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
