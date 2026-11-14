module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.PinchedEndpointTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceIntervalNaturality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.IntervalComposition
/-!
概要：区間写像空間の端点輸送と、同じ実辺による標準後合成を比較する。
方針：同じ実辺の回収と標準比較の反転を、全パラメータの随伴判定へ渡す。
規約：元の全関手と厳密切断を保持する。使われ方：一般 kernel の実 RHom 随伴。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 等しい端点の区間写像空間を、元の族を保つ同型で移す。 -/
def intervalEndpointIso {X : SSet.{v}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x' y' := by
  subst x'
  subst y'
  exact Iso.refl _

/-- pinched と区間の標準比較は、両端点の同じ等式輸送と可換。 -/
lemma pinchedInterval_endpoint {X : SSet.{v}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso hx hy).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x' y' =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y ≫ (intervalEndpointIso hx hy).hom := by
  subst x'
  subst y'
  simp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso, intervalEndpointIso, Iso.refl_hom,
    Category.id_comp, Category.comp_id]

/-- 標準関手作用と実辺の後合成の同値性は、同じ端点と辺の輸送で戻せる。 -/
lemma intervalFunctorPostcompose_equivalence_of_endpoint
    {X Y : SSet.{v}} [Quasicategory X] [Quasicategory Y]
    (F : X ⟶ Y) (x t t' : X _⦋0⦌) {px pt y py : Y _⦋0⦌}
    (e : Y.Edge (F.app (Opposite.op ⦋0⦌) t) y) (e' : Y.Edge pt py)
    (hs : t = t') (hx : F.app (Opposite.op ⦋0⦌) x = px)
    (ht : F.app (Opposite.op ⦋0⦌) t' = pt) (hy : y = py) (he : e.edge = e'.edge)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x t' ≫ (intervalEndpointIso hx ht).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose px (Truncated.HomotopyCategory.homMk e'.toTruncated))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap F x t ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose (F.app (Opposite.op ⦋0⦌) x)
          (Truncated.HomotopyCategory.homMk e.toTruncated)) := by
  subst t'
  subst px
  subst pt
  subst py
  have hh : e = e' := SSet.Edge.ext he
  subst e'
  simpa only [intervalEndpointIso, Iso.refl_hom, Category.id_comp, Category.comp_id] using h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
