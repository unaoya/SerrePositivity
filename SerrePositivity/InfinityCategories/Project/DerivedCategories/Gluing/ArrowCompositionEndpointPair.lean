module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ArrowCompositionIsoNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RestrictedDiagonalInputPair
/-!
概要：矢印 Hom と二合成対角の同型が二つの元可変辺を保持することを示す。
方針：二つの標準三角形の可変辺を回収し、同じ順序の対へまとめる。
規約：始側入力を第一成分、終側入力を第二成分に置く。
使われ方：主標的の全区間 Hom を同じ二入力付き四座標へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {X T : SSet.{u}} {a b c d : X _⦋0⦌} (f : X.Edge a b) (g : X.Edge c d)

def dgGluingArrowCompositionEndpointPair :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionPullback f g ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace a c ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace b d :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalEndpointPair (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst a g)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionSecond f d) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal a g)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionDiagonal f d)

lemma dgGluingArrowCompositionIso_inv_endpoints
    (h : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm f.edge))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm g.edge))) :
    h ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionIso f g).inv ≫ dgGluingArrowCompositionEndpointPair f g =
      lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomSourceComponent f g h) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomTargetComponent f g h) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [dgGluingArrowCompositionEndpointPair, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalEndpointPair,
      Category.assoc, lift_fst]
    rw [reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionIso_inv_last f g h,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomLastComposition, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLastFixedCompositionLift_first]
  · simp only [dgGluingArrowCompositionEndpointPair, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRestrictedDiagonalEndpointPair,
      Category.assoc, lift_snd]
    rw [reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionIso_inv_first f g h,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowHomFirstComposition, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFirstFixedCompositionLift_second]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
