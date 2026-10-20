module

public import SerrePositivity.InfinityCategories.F1.MarkedCocartesianFunctorFamilies

/-!
概要：指定辺を保つ相対関手の展開と、始域の制限およびパラメーター頂点の評価の整合性。
方針：元の相対 uncurry と関手頂点の単射性を使う。
規約：全ての等式は元の直積上の射について厳密に成り立つ。
使われ方：指定辺の条件を余極限の各項から回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 相対関手の族の制限の展開は、元の始域による直積上の制限。 -/
lemma markedCocartesianFunctorUncurry_overPre {T E B : SSet.{u}}
    (q : E ⟶ B) {a b : Over B} (i : a ⟶ b)
    (V : Set (a.left _⦋1⦌)) (W : Set (b.left _⦋1⦌))
    (hi : ∀ e ∈ V, i.left.app (Opposite.op ⦋1⦌) e ∈ W)
    (g : T ⟶ markedCocartesianFunctorSpace q b.hom W) :
    markedCocartesianFunctorUncurry (g ≫ markedCocartesianFunctorPre q i V W hi) =
      (i.left ▷ T) ≫ markedCocartesianFunctorUncurry g := by
  unfold markedCocartesianFunctorUncurry
  rw [Category.assoc, markedCocartesianFunctorPre_ι, ← Category.assoc,
    relativeFunctorOverPre_uncurry]

/-- 族の一頂点から回収した元の関手は、その頂点への実際の制限。 -/
lemma markedCocartesianFunctorUncurry_vertex {A T E B : SSet.{u}}
    {q : E ⟶ B} {a : A ⟶ B} {W : Set (A _⦋1⦌)}
    (g : T ⟶ markedCocartesianFunctorSpace q a W) (x : T _⦋0⦌) :
    ((relativeFunctorVertexEquiv q a).symm (g.app (Opposite.op ⦋0⦌) x).val).val =
      lift (𝟙 A) (SSet.const x) ≫ markedCocartesianFunctorUncurry g := by
  apply functorVertex_injective
  exact ((functorVertexEquiv A E).apply_symm_apply _).trans
    (kanFunctorVertex_parameter
      (g ≫ markedCocartesianFunctorInclusion q a W ≫ vertexFiberι _ _) x).symm

/-- 展開した同じ族は、各パラメーター頂点で始域の指定辺を cocartesian に送る。 -/
lemma markedCocartesianFunctorUncurry_cocartesian {A T E B : SSet.{u}}
    {q : E ⟶ B} {a : A ⟶ B} {W : Set (A _⦋1⦌)}
    (g : T ⟶ markedCocartesianFunctorSpace q a W) (x : T _⦋0⦌) (e : A _⦋1⦌) (he : e ∈ W) :
    IsCocartesianEdge q ((markedCocartesianFunctorUncurry g).app (Opposite.op ⦋1⦌)
      (e, PinchedHom.constant x 1)) := by
  have h := fullSubcomplexOnVertices_vertex (g.app (Opposite.op ⦋0⦌) x) e he
  change IsCocartesianEdge q
    ((((relativeFunctorVertexEquiv q a).symm (g.app (Opposite.op ⦋0⦌) x).val).val).app
      (Opposite.op ⦋1⦌) e) at h
  rw [markedCocartesianFunctorUncurry_vertex] at h
  exact h

end SerrePositivity.InfinityCategories
