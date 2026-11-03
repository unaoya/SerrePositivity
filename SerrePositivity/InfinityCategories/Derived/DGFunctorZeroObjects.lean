module
public import SerrePositivity.InfinityCategories.Derived.ContractingElementCriterion
public import SerrePositivity.InfinityCategories.DGNerve.Functor
public import SerrePositivity.DifferentialGraded.Functor.ModuleValued
public import SerrePositivity.InfinityCategories.Stable.ExactFunctor

/-! # dg 関手の nerve は実零対象を保存する

概要：任意の dg 関手は dg nerve の零頂点を全て保存する。
方針：零性から収縮元を回収し、dg 関手で移して像の実境界充填に使う。
規約：cofiber 保存や完全性全体は別途必要。使われ方：β3 の商関手・延長の零保存条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]

/-- dg nerve の関手は dg 対象の頂点を対象像の頂点へ送る。 -/
lemma dgFunctorNerve_vertex (F : DGFunctor A D E) (x : D) :
    (dgNerve.map F).app (Opposite.op ⦋0⦌) (Simplex.vertex x) = Simplex.vertex (F.obj x) := by
  apply Simplex.vertexEquiv.injective
  rfl

/-- dg 関手の像の頂点は、元の頂点の零対象性を保つ。 -/
lemma dgFunctorNerve_vertex_isZero (F : DGFunctor A D E) (x : D)
    (hx : IsZeroVertex (X := dgNerve A D) (Simplex.vertex x)) :
    IsZeroVertex (X := dgNerve A E) ((dgNerve.map F).app (Opposite.op ⦋0⦌) (Simplex.vertex x)) := by
  obtain ⟨h, dh⟩ := (dgNerve_isZeroVertex_iff_contractingElement x).1 hx
  rw [dgFunctorNerve_vertex]
  exact dgNerve_contractingElement_isZeroVertex _ ((F.map x x).f (-1) h)
    (F.map_contractingElement A x h dh)

/-- dg 関手の nerve は、選択によらず全ての実零頂点を保存する。 -/
lemma dgFunctorNerve_preservesZeroVertices (F : DGFunctor A D E) :
    PreservesZeroVertices (dgNerve.map F) := by
  intro z hz
  obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective z
  exact dgFunctorNerve_vertex_isZero F x hz

end SerrePositivity.InfinityCategories
