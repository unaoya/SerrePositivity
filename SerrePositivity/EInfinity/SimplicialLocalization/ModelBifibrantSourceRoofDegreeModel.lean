module

public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofSlices
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexUniverseOver
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseNerveCostructuredPullback

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
abbrev modelBifibrantSourceRoofProductElements :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexUniverseOver.productElements.{v, u}
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y.obj)
    (modelBifibrantSourceRoofDegree X Y q b)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductFirst : modelBifibrantSourceRoofProductElements X Y q b ⥤
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementCategory X Y q :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexUniverseOver.firstComponent.{v, u} _ _

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductFirstNerve :
    nerve (modelBifibrantSourceRoofProductElements X Y q b) ⟶
      nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementCategory X Y q) where
  app _ := ↾fun σ => σ ⋙ modelBifibrantSourceRoofProductFirst X Y q b
  naturality _ _ _ := rfl

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductOver : modelBifibrantSourceRoofProductElements X Y q b ⥤
    Over (modelBifibrantSourceRoofDegree X Y q b) := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexUniverseOver.over.{v, u} _ _

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductOverNerve :
  nerve (modelBifibrantSourceRoofProductElements X Y q b) ⟶
    nerve (Over (modelBifibrantSourceRoofDegree X Y q b)) where
  app _ := ↾fun σ => σ ⋙ modelBifibrantSourceRoofProductOver X Y q b
  naturality _ _ _ := rfl

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
def modelBifibrantSourceRoofProductIso : nerve (modelBifibrantSourceRoofProductElements X Y q b) ≅
    modelBifibrantSourceRoofDegreeModel X Y q b :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexUniverseOver.nerveIso.{v, u} _ _ ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseNerveCostructuredPullback.pullbackIso.{v, u}
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementDegree X Y q)
      (modelBifibrantSourceRoofDegree X Y q b)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductIso_source : (modelBifibrantSourceRoofProductIso X Y q b).hom ≫
    pullback.fst _ _ = modelBifibrantSourceRoofProductFirstNerve X Y q b := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseNerveCostructuredPullback.pullbackIso_source.{v, u}
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementDegree X Y q) (modelBifibrantSourceRoofDegree X Y q b)
  exact (Category.assoc _ _ _).trans (congrArg
    (fun f => (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexUniverseOver.nerveIso.{v, u}
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y.obj)
      (modelBifibrantSourceRoofDegree X Y q b)).hom ≫ f) h)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductIso_over : (modelBifibrantSourceRoofProductIso X Y q b).hom ≫
    pullback.snd _ _ = modelBifibrantSourceRoofProductOverNerve X Y q b := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseNerveCostructuredPullback.pullbackIso_over.{v, u}
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantSourceFrameElementDegree X Y q) (modelBifibrantSourceRoofDegree X Y q b)
  exact (Category.assoc _ _ _).trans (congrArg
    (fun f => (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexUniverseOver.nerveIso.{v, u}
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y.obj)
      (modelBifibrantSourceRoofDegree X Y q b)).hom ≫ f) h)

end SerrePositivity.EInfinity.SimplicialLocalization
