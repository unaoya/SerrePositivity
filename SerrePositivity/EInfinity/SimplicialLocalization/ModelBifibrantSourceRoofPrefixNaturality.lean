module

public import SerrePositivity.EInfinity.Hammock.LeftRoofPrefixNaturality
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantSourceRoofPrefixHomotopy

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
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  (X Y : HomotopicalAlgebra.BifibrantObject C)
  (q : SerrePositivity.Reedy.CofibrantResolution (C := C) SerrePositivity.Reedy.simplex X.obj)
  (b : (modelBifibrantSourceRoofTarget X Y q) _⦋0⦌)

/-- 概要：同じ bifibrant frame の実屋根・次数・全錐の比較を回収する。
方針：元の全単体と引き戻し射影の同じ三角形を使う。
規約：同じ元の比較射。使われ方：実 right Kan の余終性。 -/
lemma modelBifibrantSourceRoofProductCommaPrefixHomotopy_underMap
    {s t : modelBifibrantSourceRoofProductComma X Y q b} (a : s ⟶ t) :
    (nerveMap (Under.map a) ▷ (Δ[1] : SSet.{max u v})) ≫
      (modelBifibrantSourceRoofProductCommaPrefixHomotopy X Y q b s).h =
    (modelBifibrantSourceRoofProductCommaPrefixHomotopy X Y q b t).h ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
        ((modelBifibrantSourceRoofProductCommaDiagram X Y q b).map a))
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y) :=
  Hammock.LeftRoof.Prefix.arrowHomotopy_underMap
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory C).weakEquivalences
    (modelBifibrantSourceRoofProductCommaDiagram X Y q b)
    (modelBifibrantSourceRoofProductCommaEvaluation X Y q b)
    (modelBifibrantSourceRoofProductCommaEvaluation_weak X Y q b)
    (modelBifibrantSourceRoofProductCommaRightLeg X Y q b)
    (fun f => modelBifibrantSourceRoofProductCommaDiagram_map_weak X Y q b f) s a

end SerrePositivity.EInfinity.SimplicialLocalization
