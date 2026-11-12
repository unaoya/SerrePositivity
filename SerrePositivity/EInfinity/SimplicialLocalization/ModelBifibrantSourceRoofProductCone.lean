module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofDegreeModel
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceFrameLimits

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
open CategoryTheory Limits Opposite
open SerrePositivity.EInfinity.FrameHom
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
abbrev modelBifibrantSourceRoofProductComma :=
  CostructuredArrow (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementDegree X Y q)
  (modelBifibrantSourceRoofDegree X Y q b)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductCommaIso :
  nerve (modelBifibrantSourceRoofProductElements X Y q b) ≅
    nerve (modelBifibrantSourceRoofProductComma X Y q b) :=
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexUniverseOver.nerveIso.{v, u} _ _

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductCommaFirstNerve :
  nerve (modelBifibrantSourceRoofProductComma X Y q b) ⟶
    nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementCategory X Y q) where
  app _ := ↾fun σ => σ ⋙ CostructuredArrow.proj _ _
  naturality _ _ _ := rfl

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaIso_first :
    (modelBifibrantSourceRoofProductCommaIso X Y q b).hom ≫
      modelBifibrantSourceRoofProductCommaFirstNerve X Y q b =
        modelBifibrantSourceRoofProductFirstNerve X Y q b := rfl

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaIso_over :
    (modelBifibrantSourceRoofProductCommaIso X Y q b).hom ≫
      nerveMap (CostructuredArrow.toOver (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementDegree X Y q)
        (modelBifibrantSourceRoofDegree X Y q b)) =
          modelBifibrantSourceRoofProductOverNerve X Y q b := rfl

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
abbrev modelBifibrantSourceRoofProductCommaDegree : modelBifibrantSourceRoofProductComma X Y q b ⥤
    AsSmall.{max u v} SimplexCategory :=
  CostructuredArrow.proj _ _ ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementDegree X Y q

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
abbrev modelBifibrantSourceRoofProductCommaDiagram : modelBifibrantSourceRoofProductComma X Y q b ⥤
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).category :=
  modelBifibrantSourceRoofProductCommaDegree X Y q b ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductCommaEvaluation :
  modelBifibrantSourceRoofProductCommaDiagram X Y q b ⟶
    (Functor.const (modelBifibrantSourceRoofProductComma X Y q b)).obj
      ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q).obj (modelBifibrantSourceRoofDegree X Y q b)) where
  app s := (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q).map s.hom
  naturality {_s _t} f := by
    change (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q).map ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementDegree X Y q).map
      f.left) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q).map _ = _ ≫ 𝟙 _
    rw [← CategoryTheory.Functor.map_comp, CostructuredArrow.w, Category.comp_id]

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductCommaRightLeg :
  modelBifibrantSourceRoofProductCommaDiagram X Y q b ⟶
    (Functor.const (modelBifibrantSourceRoofProductComma X Y q b)).obj
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y) where
  app s := ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementsToDK X Y q).obj s.left).hom
  naturality {_s _t} f := by
    exact (CostructuredArrow.w ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementsToDK X Y q).map f.left)).trans
      (Category.comp_id _).symm

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductCommaAugmentation :
    modelBifibrantSourceRoofProductCommaDiagram X Y q b ⟶
      (Functor.const (modelBifibrantSourceRoofProductComma X Y q b)).obj
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C X) :=
  Functor.whiskerLeft (modelBifibrantSourceRoofProductCommaDegree X Y q b)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation X q)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaAugmentation_triangle :
    modelBifibrantSourceRoofProductCommaEvaluation X Y q b ≫
      (Functor.const (modelBifibrantSourceRoofProductComma X Y q b)).map
        ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation X q).app (modelBifibrantSourceRoofDegree X Y q b)) =
          modelBifibrantSourceRoofProductCommaAugmentation X Y q b := by
  apply NatTrans.ext
  funext s
  exact ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation X q).naturality s.hom).trans (Category.comp_id _)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaEvaluation_weak (s :
  modelBifibrantSourceRoofProductComma X Y q b) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
      ((modelBifibrantSourceRoofProductCommaEvaluation X Y q b).app s) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame_map_weak X q s.hom

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaAugmentation_weak
    (s : modelBifibrantSourceRoofProductComma X Y q b) :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
      ((modelBifibrantSourceRoofProductCommaAugmentation X Y q b).app s) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrameAugmentation_weak X q ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementDegree X Y
    q).obj s.left)

end SerrePositivity.EInfinity.SimplicialLocalization
