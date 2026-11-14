module
public import SerrePositivity.KST.SConstruction.ZeroStablePredicate
public import SerrePositivity.KST.SConstruction.SClosedPredicates
public import SerrePositivity.KST.SConstruction.StructureMapCofibers

/-! # 切断の左右に支持を持つ閉じた部分圏
概要：切断 k の右側または左側で全区間成分が零になる S_n C の安定な全部分圏を定める。
方針：各 Ar 成分の零対象条件の逆像を交差させる。
規約：全高次単体を持つ replete な全部分圏。使われ方：切断の相対 E と Segal 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 左支持は切断位置以右から始まる全区間の成分が零となる条件。 -/
def cutLeftSupport (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    ClosedStablePredicate (sStableModel n X) :=
  ClosedStablePredicate.iInter (fun a : {a : Ar.{u} n // k ≤ a.down.val.1} =>
    (zeroStablePredicate X).comap (sStableEvaluation n X (ComposableArrows.mk₀ a.val)))

/-- 右支持は切断位置以前で終わる全区間の成分が零となる条件。 -/
def cutRightSupport (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    ClosedStablePredicate (sStableModel n X) :=
  ClosedStablePredicate.iInter (fun a : {a : Ar.{u} n // a.down.val.2 ≤ k} =>
    (zeroStablePredicate X).comap (sStableEvaluation n X (ComposableArrows.mk₀ a.val)))

/-- 左支持の所属条件は右側の全区間での零性そのもの。 -/
lemma cutLeftSupport_iff (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u})
    (v : (sConstruction n X.carrier) _⦋0⦌) :
    (cutLeftSupport n k X).predicate v ↔
      ∀ a : {a : Ar.{u} n // k ≤ a.down.val.1},
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ComposableArrows.mk₀ a.val)).app
          (Opposite.op ⦋0⦌) v.val) :=
  Iff.rfl

/-- 右支持の所属条件は左側の全区間での零性そのもの。 -/
lemma cutRightSupport_iff (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u})
    (v : (sConstruction n X.carrier) _⦋0⦌) :
    (cutRightSupport n k X).predicate v ↔
      ∀ a : {a : Ar.{u} n // a.down.val.2 ≤ k},
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ComposableArrows.mk₀ a.val)).app
          (Opposite.op ⦋0⦌) v.val) :=
  Iff.rfl

/-- S_n の全頂点の対角評価は実際の零対象。 -/
lemma sConstructionVertex_diagonal_isZero {n : ℕ} {C : SSet.{u}}
    (v : (sConstruction n C) _⦋0⦌) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ComposableArrows.mk₀ (arObj i i le_rfl))).app
      (Opposite.op ⦋0⦌) v.val) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex (ComposableArrows.mk₀ (arObj i i le_rfl))
    (gappedDiagram v)
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram v) = v.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply v.val
  rw [hv] at h
  exact (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex h).mpr ((gappedDiagram_isGapped v).1 i)

/-- S_n の制限の頂点の任意の成分は元の添字の像での評価。 -/
lemma sMap_evaluate_vertex {m n : ℕ} {C : SSet.{u}}
    (θ : Fin (m + 1) →o Fin (n + 1)) (v : (sConstruction n C) _⦋0⦌)
    (a : (arNerve m) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) a).app (Opposite.op ⦋0⦌)
        ((sMap C θ).app (Opposite.op ⦋0⦌) v).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) ((arNerveMap θ).app (Opposite.op ⦋0⦌) a)).app
        (Opposite.op ⦋0⦌) v.val := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sMap_gapped_evaluate C θ a) (Opposite.op ⦋0⦌)) v
  exact h

end SerrePositivity.KST.SConstruction
