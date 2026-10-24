module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionCoreLift

/-!
概要：始域の頂点を覆う制限によって、section の core への所属を降下させる。
方針：各頂点を一つの項から取り、制限と評価の可換性で可逆性を回収する。
規約：被覆の各項の単射性や充填性を要求しない。
使われ方：境界とセルで貼り合わせた元の section の族を core の族に戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 始域の全頂点を覆う族の各制限で可逆なら、元の section の辺は可逆。 -/
lemma isInvertibleEdge_cocartesianSection_of_vertex_cover
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [InnerFibration p]
    {J : Type v} (a : Over B) (D : J → Over B) (i : ∀ j, D j ⟶ a)
    (hi : ∀ x : a.left _⦋0⦌, ∃ j y, (i j).left.app (Opposite.op ⦋0⦌) y = x)
    {v w : (SerrePositivity.InfinityCategories.cocartesianSections p a.hom) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (SerrePositivity.InfinityCategories.cocartesianSections p a.hom)) v w)
    (he : ∀ j, IsInvertibleEdge (X := SerrePositivity.InfinityCategories.cocartesianSections p (D j).hom)
      (e.map ((truncation 2).map (SerrePositivity.InfinityCategories.cocartesianSectionsPre p (i j))))) :
    IsInvertibleEdge e := by
  apply (isInvertibleEdge_cocartesianSection_iff_evaluate p a.hom e).mpr
  intro x
  obtain ⟨j, y, rfl⟩ := hi x
  have h := (he j).map (cocartesianSectionEvaluate p (D j).hom y)
  apply (isInvertibleEdge_congr
    (e := (e.map ((truncation 2).map (SerrePositivity.InfinityCategories.cocartesianSectionsPre p (i j)))).map
      ((truncation 2).map (cocartesianSectionEvaluate p (D j).hom y)))
    (f := e.map ((truncation 2).map
      (cocartesianSectionEvaluate p a.hom ((i j).left.app (Opposite.op ⦋0⦌) y)))) ?_).mp h
  exact congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) e.edge)
    (cocartesianSectionEvaluate_overPre p (i j) y)

/-- core に属する局所的な族を回収する section の族は、元の core に厳密に持ち上がる。 -/
def cocartesianSectionCoreLift_of_vertex_cover
    {T E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [InnerFibration p]
    {J : Type v} (a : Over B) (D : J → Over B) (i : ∀ j, D j ⟶ a)
    (hi : ∀ x : a.left _⦋0⦌, ∃ j y, (i j).left.app (Opposite.op ⦋0⦌) y = x)
    (g : T ⟶ SerrePositivity.InfinityCategories.cocartesianSections p a.hom)
    (s : ∀ j, T ⟶ (quasicategoryCore (SerrePositivity.InfinityCategories.cocartesianSections p (D j).hom) : SSet.{u}))
    (hs : ∀ j, g ≫ SerrePositivity.InfinityCategories.cocartesianSectionsPre p (i j) =
      s j ≫ (quasicategoryCore (SerrePositivity.InfinityCategories.cocartesianSections p (D j).hom)).ι) :
    T ⟶ (quasicategoryCore (SerrePositivity.InfinityCategories.cocartesianSections p a.hom) : SSet.{u}) :=
  quasicategoryCoreLift g (by
    intro e
    apply isInvertibleEdge_cocartesianSection_of_vertex_cover p a D i hi
    intro j
    have hh := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) e) (hs j)
    exact (isInvertibleEdge_congr
      (e := (edgeOfSimplex (g.app (Opposite.op ⦋1⦌) e)).map
        ((truncation 2).map (SerrePositivity.InfinityCategories.cocartesianSectionsPre p (i j))))
      (f := edgeOfSimplex ((s j).app (Opposite.op ⦋1⦌) e).val) hh).mpr
        (quasicategoryCore_edge _))

end SerrePositivity.InfinityCategories
