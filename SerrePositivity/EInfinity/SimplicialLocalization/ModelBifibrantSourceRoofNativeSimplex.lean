module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismSimplex
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofPrefixPath

/-!
概要：元の bifibrant frame の全屋根を同じ次数・積単体・実 slice の図式で回収する。
方針：元の全単体の比較と同じ引き戻しの射影・全三角形を使う。
規約：元の解像・指定点・全錐を保持する。
使われ方：実 right Kan 次数比較の余終性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SSet SimplicialLocalization
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductCommaNativeSimplex {n : ℕ}
    (Γ : Fin (n + 1) ⥤ modelBifibrantSourceRoofProductComma X Y q b)
    (t : Fin (n + 1) →o Fin 2) :
    (kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) _⦋n + 1⦌ :=
  RoofPrefix.simplex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)
    (modelBifibrantSourceRoofProductCommaDiagram X Y q b)
    (modelBifibrantSourceRoofProductCommaEvaluation X Y q b)
    (modelBifibrantSourceRoofProductCommaEvaluation_weak X Y q b)
    (modelBifibrantSourceRoofProductCommaRightLeg X Y q b)
    (fun f => modelBifibrantSourceRoofProductCommaDiagram_map_weak X Y q b f) Γ t

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaNativeSimplex_target {n : ℕ}
    (Γ : Fin (n + 1) ⥤ modelBifibrantSourceRoofProductComma X Y q b)
    (t : Fin (n + 1) →o Fin 2) :
    (kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op
      (modelBifibrantSourceRoofProductCommaNativeSimplex X Y q b Γ t) =
      modelBifibrantHammockVertex Y :=
  (RoofPrefix.simplex_target (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)
    (modelBifibrantSourceRoofProductCommaDiagram X Y q b)
    (modelBifibrantSourceRoofProductCommaEvaluation X Y q b)
    (modelBifibrantSourceRoofProductCommaEvaluation_weak X Y q b)
    (modelBifibrantSourceRoofProductCommaRightLeg X Y q b)
    (fun f => modelBifibrantSourceRoofProductCommaDiagram_map_weak X Y q b f) Γ t).trans
      (hammockLocalizationNerveMap_vertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)).symm

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductCommaNativeSliceSimplex {n : ℕ}
    (Γ : Fin (n + 1) ⥤ modelBifibrantSourceRoofProductComma X Y q b)
    (t : Fin (n + 1) →o Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm (modelBifibrantHammockVertex Y))) _⦋n⦌ := by
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
    (modelBifibrantSourceRoofProductCommaNativeSimplex X Y q b Γ t), ?_⟩
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inr,
    SSet.yonedaEquiv_symm_naturality_left]
  exact congrArg (fun z : (kanHammockNerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C)) _⦋0⦌ =>
    SSet.yonedaEquiv.symm z) (modelBifibrantSourceRoofProductCommaNativeSimplex_target X Y q b Γ t)

end SerrePositivity.EInfinity.SimplicialLocalization
