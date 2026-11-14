module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ArrowCalculus.ArrowIntervalCompositionEndpoints
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.IntervalPostEndpointNaturality
/-!
概要：任意の同じ矢印頂点を持つ区間 Hom の座標変更は二端評価と可換である。
方針：端点の等式輸送を一般形で相殺して元の二合成対応へ戻す。
規約：全区間と四頂点を保持する。使われ方：元 lax Hom 標的の座標輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
variable {Z : SSet.{u}} {a b c d : Z _⦋0⦌} (f : Z.Edge a b) (g : Z.Edge c d)
  {x y : ((ihom (Δ[1] : SSet.{u})).obj Z) _⦋0⦌}
  (hx : x = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm f.edge))
  (hy : y = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm g.edge))

def dgGluingArrowCoordinateIso :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.intervalEndpointIso hx hy ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionIso f g).symm

def dgGluingArrowBaseCoordinateIso :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.intervalEndpointIso
    ((congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair Z).app (Opposite.op ⦋0⦌)) hx).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowEndpointPair_vertex f))
    ((congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair Z).app (Opposite.op ⦋0⦌)) hy).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowEndpointPair_vertex g)) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalMappingProductIso (X := Z) (Y := Z) a c b d).symm

lemma dgGluingArrowCoordinateIso_endpoints :
    (dgGluingArrowCoordinateIso f g hx hy).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair Z) x y rfl rfl ≫
        (dgGluingArrowBaseCoordinateIso f g hx hy).hom =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionEndpointPair f g := by
  rw [dgGluingArrowCoordinateIso, Iso.trans_inv, Iso.symm_inv,
    dgGluingArrowBaseCoordinateIso, Iso.trans_hom]
  simp only [Category.assoc]
  rw [reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIntervalPostOfEq_endpoint_naturality]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingArrowCompositionIso_hom_endpoints f g

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
