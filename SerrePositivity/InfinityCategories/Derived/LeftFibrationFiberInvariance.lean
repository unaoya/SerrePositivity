module
public import SerrePositivity.InfinityCategories.F1.LeftFibrationTransportNaturality
public import SerrePositivity.InfinityCategories.F1.InvertibleLeftTransport
public import SerrePositivity.InfinityCategories.Derived.DGFiberTransportSquare
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorPrecomposition
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
/-!
概要：同じ left fibration の fiber 射と相対前合成の同値性を、可逆な底の辺へ沿って移す。
方針：実辺輸送の自然性同型と両輸送の同値を使う。
規約：底も動く同じ正方形を保持する。使われ方：Hom 試験による錐の切断制限の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
/-- 同じ実輸送と相対切断の同値性の不変性。 -/
lemma leftFibrationFiberMap_isQCatEquivalence_iff_of_invertibleEdge
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p)
    {a b : B _⦋0⦌} (e : SSet.Edge a b) (he : IsInvertibleEdge e) :
    IsQCatEquivalence (vertexFiberMap p q f hf a) ↔
      IsQCatEquivalence (vertexFiberMap p q f hf b) := by
  have hp := edgeTransport_isQCatEquivalence_of_isInvertibleEdge p e he
  have hq := edgeTransport_isQCatEquivalence_of_isInvertibleEdge q e he
  have hn := leftFibrationMap_transportIso p q f hf e
  constructor
  · intro ha
    exact hp.cancel_left ((ha.comp hq).ofFunctorIso hn.symm)
  · intro hb
    exact hq.cancel_right ((hp.comp hb).ofFunctorIso hn)
end SerrePositivity.InfinityCategories

namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
/-- 同じ実輸送と相対切断の同値性の不変性。 -/
lemma leftFibrationSquareFiber_isQCatEquivalence_iff_of_invertibleEdge
    {E B F D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) (q : F ⟶ D) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g)
    {a b : B _⦋0⦌} (e : SSet.Edge a b) (he : IsInvertibleEdge e) :
    IsQCatEquivalence (transportSquareFiberMap p q f g h a) ↔
      IsQCatEquivalence (transportSquareFiberMap p q f g h b) := by
  have hp := edgeTransport_isQCatEquivalence_of_isInvertibleEdge p e he
  have hq := edgeTransport_isQCatEquivalence_of_isInvertibleEdge q (e.map g) (he.map g)
  have hn := dgLeftFibrationSquareTransportIso p q f g h e
  constructor
  · intro ha
    exact hp.cancel_left ((ha.comp hq).ofFunctorIso hn.symm)
  · intro hb
    exact hq.cancel_right ((hp.comp hb).ofFunctorIso hn)
end SerrePositivity.InfinityCategories

namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
/-- 同じ実輸送と相対切断の同値性の不変性。 -/
lemma relativeFunctorPre_isQCatEquivalence_iff_of_functorIso
    {A D E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (i : D ⟶ A)
    {a b : A ⟶ B} (e : FunctorIso a b) :
    IsQCatEquivalence (relativeFunctorPre p a i) ↔
      IsQCatEquivalence (relativeFunctorPre p b i) := by
  have h := leftFibrationSquareFiber_isQCatEquivalence_iff_of_invertibleEdge
    ((ihom A).map p) ((ihom D).map p) ((pre i).app E) ((pre i).app B)
    ((pre i).naturality p).symm (SSet.Edge.ofTruncated e.edge) e.edge_isInvertible
  exact h
end SerrePositivity.InfinityCategories
