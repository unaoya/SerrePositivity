module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.FunctorIso
public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldMapping
public import SerrePositivity.InfinityCategories.F1.FullSubcomplexEquivalenceLifting

/-!
概要：相対関手の cocartesian 条件と scaffold の水平辺条件の同型不変性。
方針：相対関手空間の包含で頂点の同型を通常の関手同型へ写す。
規約：相対関手の元の頂点と全高次を保持する。
使われ方：同型不変な全部分複体への前合成同値の制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 相対関手の頂点の同型は、その元の通常の関手の同型を与える。 -/
def relativeFunctorVertex_functorIso {A E B : SSet.{u}} (q : E ⟶ B) (a : A ⟶ B)
    {f g : A ⟶ E} (hf : f ≫ q = a) (hg : g ≫ q = a)
    (h : VertexIso (relativeFunctorVertex q a f hf) (relativeFunctorVertex q a g hg)) :
    FunctorIso f g :=
  VertexIso.map h (vertexFiberι ((ihom A).map q) (functorVertex a))

/-- 元の cocartesian 関手を表す頂点条件は、相対関手空間の同型で不変。 -/
lemma cocartesianRelativeFunctorPredicate_iff_of_vertexIso {A E B : SSet.{u}}
    [Quasicategory B] (p : A ⟶ B) (q : E ⟶ B) [InnerFibration q]
    {v w : (relativeFunctorSpace q p) _⦋0⦌} (h : VertexIso v w) :
    cocartesianRelativeFunctorPredicate p q v ↔ cocartesianRelativeFunctorPredicate p q w := by
  let : Quasicategory E := quasicategory_of_innerFibration q
  obtain ⟨f, hf, rfl⟩ := exists_relativeFunctorVertex q p v
  obtain ⟨g, hg, rfl⟩ := exists_relativeFunctorVertex q p w
  rw [cocartesianRelativeFunctorPredicate_vertex, cocartesianRelativeFunctorPredicate_vertex]
  exact preservesCocartesianEdges_iff_of_functorIso p q
    (relativeFunctorVertex_functorIso q p hf hg h)

/-- 水平辺を保つ scaffold 関手の頂点条件は、相対関手空間の同型で不変。 -/
lemma cocartesianScaffoldFunctorPredicate_iff_of_vertexIso
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {D : SSet.{u}}
    (q : D ⟶ nerve C) [InnerFibration q]
    {v w : (relativeFunctorSpace q (simplicialReplacementProjection F)) _⦋0⦌}
    (h : VertexIso v w) :
    CocartesianScaffoldFunctorPredicate F q v ↔ CocartesianScaffoldFunctorPredicate F q w := by
  let : Quasicategory D := quasicategory_of_innerFibration q
  obtain ⟨f, hf, rfl⟩ := exists_relativeFunctorVertex q (simplicialReplacementProjection F) v
  obtain ⟨g, hg, rfl⟩ := exists_relativeFunctorVertex q (simplicialReplacementProjection F) w
  rw [cocartesianScaffoldFunctorPredicate_vertex, cocartesianScaffoldFunctorPredicate_vertex]
  have hi := relativeFunctorVertex_functorIso q (simplicialReplacementProjection F) hf hg h
  constructor <;> intro hc c d k x
  · exact (isCocartesianEdge_iff_of_functorIso q hi _).mp (hc k x)
  · exact (isCocartesianEdge_iff_of_functorIso q hi _).mpr (hc k x)

end SerrePositivity.InfinityCategories
