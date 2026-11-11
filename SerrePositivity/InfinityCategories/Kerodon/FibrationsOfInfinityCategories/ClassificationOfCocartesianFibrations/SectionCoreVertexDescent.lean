module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SectionCoreLift

/-!
概要：始域の頂点を覆う制限によって、section の core への所属を降下させる。
方針：各頂点を一つの項から取り、制限と評価の可換性で可逆性を回収する。
規約：被覆の各項の単射性や充填性を要求しない。
使われ方：境界とセルで貼り合わせた元の section の族を core の族に戻す。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 始域の全頂点を覆う族の各制限で可逆なら、元の section の辺は可逆。 -/
lemma isInvertibleEdge_cocartesianSection_of_vertex_cover
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [InnerFibration p]
    {J : Type v} (a : Over B) (D : J → Over B) (i : ∀ j, D j ⟶ a)
    (hi : ∀ x : a.left _⦋0⦌, ∃ j y, (i j).left.app (Opposite.op ⦋0⦌) y = x)
    {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a.hom) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a.hom)) v w)
    (he : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p (D j).hom)
      (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p (i j))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isInvertibleEdge_cocartesianSection_iff_evaluate p a.hom e).mpr
  intro x
  obtain ⟨j, y, rfl⟩ := hi x
  have h := (he j).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate p (D j).hom y)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p (i j)))).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate p (D j).hom y)))
    (f := e.map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate p a.hom ((i j).left.app (Opposite.op ⦋0⦌) y)))) ?_).mp h
  exact congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) e.edge)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionEvaluate_overPre p (i j) y)

/-- core に属する局所的な族を回収する section の族は、元の core に厳密に持ち上がる。 -/
def cocartesianSectionCoreLift_of_vertex_cover
    {T E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [InnerFibration p]
    {J : Type v} (a : Over B) (D : J → Over B) (i : ∀ j, D j ⟶ a)
    (hi : ∀ x : a.left _⦋0⦌, ∃ j y, (i j).left.app (Opposite.op ⦋0⦌) y = x)
    (g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a.hom)
    (s : ∀ j, T ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p (D j).hom) : SSet.{u}))
    (hs : ∀ j, g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p (i j) =
      s j ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p (D j).hom)).ι) :
    T ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a.hom) : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift g (by
    intro e
    apply isInvertibleEdge_cocartesianSection_of_vertex_cover p a D i hi
    intro j
    have hh := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) e) (hs j)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (g.app (Opposite.op ⦋1⦌) e)).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p (i j))))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((s j).app (Opposite.op ⦋1⦌) e).val) hh).mpr
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge _))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
