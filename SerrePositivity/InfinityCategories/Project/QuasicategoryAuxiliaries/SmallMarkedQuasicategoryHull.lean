module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallQuasicategoryHull
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SmallInverseWitnessSeed

/-!
概要：指定可逆辺を保ち、全小図式を同じ包含へ因子化する小さい quasicategory。
方針：逆三角形を種に加えてから内ホーン閉包と Shrink を行う。
規約：指定辺の可逆性の保持を実三角形から証明する。
使われ方：Ind-S (4) の大きい標的での反転条件の小模型への回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

variable {X : SSet.{v}} [Quasicategory X] (A : X.Subcomplex)
    {ι : Type w}
    (s : ι → X _⦋1⦌) (hs : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (s i)))

/-- 元の小さい種と、同じ指定辺の逆三角形を含む種。 -/
def markedSeed : X.Subcomplex := A ⊔ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.inverseWitnessSeed s hs

instance small_markedSeed [∀ d, Small.{u} (A.obj d)] [Small.{u} ι]
    (d : SimplexCategoryᵒᵖ) :
    Small.{u} ((markedSeed A s hs).obj d) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.small_inverseWitnessSeed.{u} s hs d
  change Small.{u} ↥(A.obj d ∪ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.inverseWitnessSeed s hs).obj d)
  infer_instance

variable {X : SSet.{max u v}} [Quasicategory X] (A : X.Subcomplex)
    [∀ d, Small.{u} (A.obj d)] {ι : Type w} [Small.{u} ι]
    (s : ι → X _⦋1⦌) (hs : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (s i)))

/-- 指定可逆辺の逆三角形を持つ同じ閉包から構成する小模型。 -/
def markedHull : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.Hull.{u, v} X (markedSeed A s hs) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hull (markedSeed A s hs)

/-- 同じ包含の像が指定辺なら、その辺は小模型でも可逆。 -/
lemma markedHull_reflects_edge (i : ι)
    {x y : ((SSet.uliftFunctor.{v, u}).obj (markedHull.{u, v} A s hs).obj) _⦋0⦌}
    (e : Truncated.Edge
      (X := (truncation 2).obj ((SSet.uliftFunctor.{v, u}).obj (markedHull.{u, v} A s hs).obj)) x y)
    (he : (markedHull.{u, v} A s hs).inclusion.app (Opposite.op ⦋1⦌) e.edge = s i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  let C := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.innerHornClosure (markedSeed A s hs)
  have (d : SimplexCategoryᵒᵖ) : Small.{u} (C.toSSet.obj d) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.small_innerHornClosure (markedSeed A s hs) d
  let q := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.modelIso.{u, v} C.toSSet
  let eC := e.map ((truncation 2).map q.hom)
  have hC : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.inverseWitnessSeed s hs ≤ C :=
    le_trans le_sup_right (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.le_innerHornClosure (markedSeed A s hs))
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge eC := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.inverseWitnessSeed_reflects_edge s hs C hC i eC he
  have h' := h.map q.inv
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := eC.map ((truncation 2).map q.inv)) (f := e) ?_).mp h'
  change q.inv.app _ (q.hom.app _ e.edge) = e.edge
  have hr := NatTrans.congr_app q.hom_inv_id (Opposite.op ⦋1⦌)
  exact ConcreteCategory.congr_hom hr e.edge

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
