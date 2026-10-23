module

public import SerrePositivity.InfinityCategories.F1.Transport.LocalizationUlift

/-!
概要：指定辺を反転する任意の関手を、宇宙を合わせた元の底へ coherent に降下する。
方針：関手を反転関手の頂点で表し、局所化の同値の逆と大域的な比較を適用する。
規約：底・標的の表示は変更せず、前合成との関手同型を明示する。
使われ方：全 left fibrations の共同切断評価を一つの分類図式へ降ろす。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 指定辺を反転する関手を、その反転関手の全部分複体の頂点として表示する。 -/
def invertingFunctorVertex {X E : SSet.{u}} (W : Set (X _⦋1⦌)) (F : X ⟶ E)
    (hF : InvertsEdges F W) : (invertingFunctors X E W : SSet.{u}) _⦋0⦌ :=
  ⟨functorVertex F, by
    intro t
    have ht : t = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [ht, op_id, Functor.map_id_apply]
    change InvertsEdges ((functorVertexEquiv X E).symm ((functorVertexEquiv X E) F)) W
    rw [Equiv.symm_apply_apply]
    exact hF⟩

/-- 反転関手の頂点を周囲の関手空間へ戻すと、指定した関手の頂点そのもの。 -/
lemma invertingFunctorVertex_val {X E : SSet.{u}} (W : Set (X _⦋1⦌)) (F : X ⟶ E)
    (hF : InvertsEdges F W) : (invertingFunctorVertex W F hF).val = functorVertex F := rfl

/-- 反転関手を、元の底を共通の宇宙へ持ち上げた上の関手へ降下する。 -/
def transportUliftFunctorDescent (B : SSet.{u}) {E : SSet.{max u v}} [Quasicategory E]
    (F : (SSet.uliftFunctor.{v, u}).obj (nerve (TransportSimplexCategory B)) ⟶ E)
    (hF : InvertsEdges F (ULift.up '' transportSimplexInitialEdges B)) :
    (SSet.uliftFunctor.{v, u}).obj B ⟶ E :=
  (functorVertexEquiv _ E).symm
    ((transportSimplexUliftInvertingDescent B E).app (Opposite.op ⦋0⦌)
      (invertingFunctorVertex _ F hF))

/-- 降下した関手を持ち上げた初頂点写像へ制限すると、元の関手と coherent に同型。 -/
def transportUliftFunctorDescentIso (B : SSet.{u}) {E : SSet.{max u v}} [Quasicategory E]
    (F : (SSet.uliftFunctor.{v, u}).obj (nerve (TransportSimplexCategory B)) ⟶ E)
    (hF : InvertsEdges F (ULift.up '' transportSimplexInitialEdges B)) :
    FunctorIso
      ((SSet.uliftFunctor.{v, u}).map (transportSimplexFirstVertexMap B) ≫
        transportUliftFunctorDescent B F hF) F := by
  have hv : functorVertex (transportUliftFunctorDescent B F hF) =
      (transportSimplexUliftInvertingDescent B E).app (Opposite.op ⦋0⦌)
        (invertingFunctorVertex _ F hF) :=
    (functorVertexEquiv _ E).apply_symm_apply _
  change VertexIso
    (((pre ((SSet.uliftFunctor.{v, u}).map (transportSimplexFirstVertexMap B))).app E).app
      (Opposite.op ⦋0⦌) (functorVertex (transportUliftFunctorDescent B F hF))) (functorVertex F)
  rw [hv]
  exact (transportSimplexUliftInvertingDescentFamilyIso B E).app (invertingFunctorVertex _ F hF)

end SerrePositivity.InfinityCategories
