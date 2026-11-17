module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixPrismZeroSlice
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofNativePrism
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofProductFunctorCell

/-!
# 元の実 native prism の零端は同じ通常右脚の全円柱

概要：零端の通常右余錐表示を任意可換環の実 comma へ代入する。
方針：同じ頂点表示の等号と全 slice 単体の値の一致を使う。
規約：元の qY・元の全右脚・元の円柱を保持する。
使われ方：native roof 全三角形の零端条件 hb。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits SSet MonoidalCategory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories
open scoped Simplicial

private lemma uncurry_point_ext {S E : SSet.{u}} {p q : (Δ[0] : SSet.{u}) ⟶ E}
    (h : p = q) (f : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) (g : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver q)
    (hv : ∀ (n : ℕ) (a : S _⦋n⦌), (f.app (Opposite.op ⦋n⦌) a).val =
      (g.app (Opposite.op ⦋n⦌) a).val) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry g := by
  subst q
  have he : f = g := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro a
    exact Subtype.ext (hv n a)
  rw [he]

variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

lemma cofibrantSourceRoofProductCommaNativePrism_zero_uncurry :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ cofibrantSourceRoofProductCommaNativePrism A X Y b) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCoconeEquiv (Cocone.mk
        (show (cofibrantAlgebraRelativeCategory A).category from Y)
        (cofibrantSourceRoofProductCommaRightLeg A X Y b))).val ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A) := by
  let P := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.prism (cofibrantAlgebraRelativeCategory A)
    (cofibrantSourceRoofProductCommaDiagram A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation_weak A X Y b)
    (cofibrantSourceRoofProductCommaRightLeg A X Y b)
    (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f)
  have hq := congrArg (fun z : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockNerve (cofibrantAlgebraRelativeCategory A)) _⦋0⦌ =>
    SSet.yonedaEquiv.symm z)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap_vertex (cofibrantAlgebraRelativeCategory A)
      (show (cofibrantAlgebraRelativeCategory A).category from Y))
  refine (uncurry_point_ext hq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ cofibrantSourceRoofProductCommaNativePrism A X Y b)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ P) (fun _ _ => rfl)).trans ?_
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.prism_zero_uncurry (cofibrantAlgebraRelativeCategory A)
    (cofibrantSourceRoofProductCommaDiagram A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation_weak A X Y b)
    (cofibrantSourceRoofProductCommaRightLeg A X Y b)
    (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f)

lemma cofibrantSourceRoofProductCommaNativePrism_zero_evaluation :
    (β_ (nerve (cofibrantSourceRoofProductComma A X Y b)) (Δ[1] : SSet.{u + 1})).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ cofibrantSourceRoofProductCommaNativePrism A X Y b) =
    (cofibrantSourceRoofProductCommaRightHomotopy A X Y b).h := by
  rw [cofibrantSourceRoofProductCommaNativePrism_zero_uncurry A X Y b]
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nerveCoconePrism_eq_natTrans
    (cofibrantSourceRoofProductCommaDiagram A X Y b)
    (Cocone.mk (show (cofibrantAlgebraRelativeCategory A).category from Y)
      (cofibrantSourceRoofProductCommaRightLeg A X Y b))
  exact (congrArg (fun f => f ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)) h)

end SerrePositivity.EInfinity.BarrattEccles
