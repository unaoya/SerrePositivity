module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.LaxPullbacks.LaxHomIntervalInputCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.LaxHomIntervalCoordinatesComparison
/-!
概要：正本標的の区間座標を既存の元二入力付き四座標標的へ厳密同型で結ぶ。
方針：底の同じ区間 Hom を二作用の積へ移し、三成分が同型である pullback.map を用いる。
規約：矢印座標・左右 Hom 入力・底の適合条件をすべて保持する。
使われ方：入力付き四座標比較の同値性と実逆射を元の正本比較へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

def dgGluingLaxHomCoordinateTargetIso :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomIntervalCoordinates R C D M X Y ≅
      pullback
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionEndpointPair (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M X)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedAugmentationEdge R C D M Y))
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLeftCoefficientInput R C D M X Y) ⊗ₘ
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedRightCoefficientInput R C D M X Y)) :=
  asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomIntervalBaseCoordinateIso R C D M X Y).hom
    (by simpa only [Category.assoc, Category.id_comp] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomIntervalEndpointMap_coordinates R C D M X Y)
    (by simpa only [Category.assoc, Category.id_comp] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomIntervalInputMap_coordinates R C D M X Y))

lemma dgGluingLaxHomCoordinateTargetIso_arrow :
    (dgGluingLaxHomCoordinateTargetIso R C D M X Y).hom ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
lemma dgGluingLaxHomCoordinateTargetIso_inputs :
    (dgGluingLaxHomCoordinateTargetIso R C D M X Y).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

lemma dgGluingLaxHomCoordinateTargetIso_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomPullbackComparison R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomIntervalCoordinatesTransport R C D M X Y ≫
        (dgGluingLaxHomCoordinateTargetIso R C D M X Y).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomInputCoordinateComparison R C D M X Y := by
  apply pullback.hom_ext
  · simp only [Category.assoc, dgGluingLaxHomCoordinateTargetIso_arrow]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomIntervalCoordinatesComparison_arrow R C D M X Y
  · simp only [Category.assoc, dgGluingLaxHomCoordinateTargetIso_inputs]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomIntervalCoordinatesComparison_inputs R C D M X Y
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
