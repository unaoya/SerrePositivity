module
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphExtendedNativeComparison
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphPerfectExtendedArrow
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomotopyInputExchange

/-!
概要：同じ二 graph の実 Perf 延長比較は元比較射を保って全自然である。
方針：共通比較族の自然性を同じ実二成分へ端点だけ正規化して輸送する。
規約：実延長の元射を共役で置換しない。使われ方：固定 ν の実中央射比較への接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (B E : Type (max (u + 1) v))
  [DGCategory R B] [Small.{u} B] [DGCategory R E] [Small.{u} E]
  (F G : DGFunctor R B B) (τ : DGFunctorParamTrans R B B (𝟙_ (Complex R)) F G)
local notation "P" => DGCategoryCellResolution.Source R B
local notation "Fp" => dgCellResolvedGraphPerfectFunctor R B F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R B F)
local notation "Gp" => dgCellResolvedGraphPerfectFunctor R B G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R B G)

/-- 概要：元比較の同じ native graph 射と実 Perf 延長射を二つの全比較が結ぶ。
方針：共通 Perf 比較族の交換 square を指定した四端点へ輸送する。
規約：元比較射・元商延長・二成分の比較値を保持。
使われ方：native square と保存済み実中央比較の主接続。 -/
lemma dgCellResolvedGraphPerfectExtendedNativeComparison_naturality
    (projection : DGFunctor R (P) E) :
    (dgCellGraphExtendedNativeFunctor R B E projection).map (dgCellResolvedGraphMap R B F G τ) ≫
      (dgCellResolvedGraphPerfectExtendedNativeComparison R B E G projection).hom =
    (dgCellResolvedGraphPerfectExtendedNativeComparison R B E F projection).hom ≫
      dgCellResolvedGraphPerfectExtendedNerveArrow R B E F G τ projection := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Fp)
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Gp)
  let a := dgCellResolvedGraphPerfectNerveArrow R B F G τ
  let e := dgCellPerfectExtensionNativeFamily R B E projection
  let cF := dgCellResolvedGraphPerfectExtendedNativeComparison R B E F projection
  let cG := dgCellResolvedGraphPerfectExtendedNativeComparison R B E G projection
  have sF := dgCellResolvedGraphPerfectNativeFamily_source R B E F projection
  have sG := dgCellResolvedGraphPerfectNativeFamily_source R B E G projection
  have tF := dgCellResolvedGraphPerfectNativeFamily_target R B E F projection
  have tG := dgCellResolvedGraphPerfectNativeFamily_target R B E G projection
  have hF := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq cF (e.precomp f) sF.symm tF.symm
    (dgCellResolvedGraphPerfectExtendedNativeComparison_family_heq R B E F projection)
  have hG := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq cG (e.precomp g) sG.symm tG.symm
    (dgCellResolvedGraphPerfectExtendedNativeComparison_family_heq R B E G projection)
  have hA := dgCellResolvedGraphPerfectNativeAction_heq R B E F G τ projection
  have hB := dgCellResolvedGraphPerfectExtendedNerveArrow_family_heq R B E F G τ projection
  have hL := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_comp_heq _ cG.hom _ (e.precomp g).hom
    sF.symm sG.symm tG.symm hA.symm hG
  have hR := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_comp_heq cF.hom _ (e.precomp f).hom _
    sF.symm tF.symm tG.symm hF hB
  have hN := dgCellPerfectExtensionNativeFamily_naturality R B E projection f g a
  exact eq_of_heq (hL.trans ((heq_of_eq hN).trans hR.symm))

end SerrePositivity.KST.SConstruction
