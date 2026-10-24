module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldPullbackLifts
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackLiftPreservation
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackHomRestriction
public import SerrePositivity.InfinityCategories.F1.Cocartesian.MarkedCocartesianFunctorPrecomposition

/-!
概要：部分底上の元の cocartesian Hom を、同じ比較の像の辺を保つ scaffold Hom へ制限する。
方針：実際の cocartesian 辺の逆像を指定し、同じ始点の水平 lift で保存条件を反映する。
規約：部分底の充填性や辺保存の追加仮定を置かない。
使われ方：全相対 Hom の比較同値を元の辺保存 Hom へ制限する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] {E F : SSet.{u}}
  (p : E ⟶ nerve C) (q : F ⟶ nerve C) (a : Over (nerve C))

/-- 同じ引き戻し比較の像が実際に cocartesian となる scaffold の指定辺。 -/
def cocartesianScaffoldPullbackMark :
    Set ((pullback a.hom
      (simplicialReplacementProjection (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p))) _⦋1⦌) :=
  {d | IsCocartesianEdge (pullback.fst a.hom p)
    ((cocartesianScaffoldPullbackOverMap p a).left.app (Opposite.op ⦋1⦌) d)}

/-- 指定辺を元の標的の cocartesian 辺へ送る scaffold の全相対 Hom。 -/
def cocartesianScaffoldPullbackMarkedHom : SSet.{u} :=
  markedCocartesianFunctorSpace q
    (pullback.snd a.hom
      (simplicialReplacementProjection (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p)) ≫
        simplicialReplacementProjection (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p))
    (cocartesianScaffoldPullbackMark p a)

/-- 元の辺保存 Hom に作用する、同じ scaffold の前合成。 -/
def cocartesianScaffoldPullbackMarkedPre :
    cocartesianPullbackHomSpace p q a ⟶ cocartesianScaffoldPullbackMarkedHom p q a :=
  markedCocartesianFunctorPre q (cocartesianScaffoldPullbackOverMap p a)
    (cocartesianScaffoldPullbackMark p a) {e | IsCocartesianEdge (pullback.fst a.hom p) e}
    (fun _ h ↦ h)

/-- 同じ scaffold への前合成は、部分底上でも元の全 cocartesian 辺の保存を反映する。 -/
lemma cocartesianScaffoldPullbackMarkedPredicate_reflect
    [CocartesianFibration p] [InnerFibration q]
    (v : (relativeFunctorSpace q (pullback.snd a.hom p ≫ p)) _⦋0⦌)
    (hv : markedCocartesianFunctorPredicate q
      (pullback.snd a.hom
        (simplicialReplacementProjection (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p)) ≫
          simplicialReplacementProjection (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p))
      (cocartesianScaffoldPullbackMark p a)
      ((cocartesianScaffoldPullbackRawHomPre p q a).app (Opposite.op ⦋0⦌) v)) :
    markedCocartesianFunctorPredicate q (pullback.snd a.hom p ≫ p)
      {e | IsCocartesianEdge (pullback.fst a.hom p) e} v := by
  obtain ⟨H, hH, rfl⟩ := exists_relativeFunctorVertex q _ v
  change markedCocartesianFunctorPredicate q _ _
    ((relativeFunctorOverPre q (cocartesianScaffoldPullbackOverMap p a)).app _
      (relativeFunctorVertex q _ H hH)) at hv
  rw [relativeFunctorOverPre_vertex, markedCocartesianFunctorPredicate_vertex] at hv
  rw [markedCocartesianFunctorPredicate_vertex]
  apply preservesCocartesianPullbackEdges_of_matching_lifts p q a H
  intro e
  obtain ⟨d, hs, hb, hc⟩ := exists_cocartesianScaffoldPullbackMatchingLift p a e
  refine ⟨(cocartesianScaffoldPullbackOverMap p a).left.app _ d, hs, hb, hc, ?_⟩
  exact hv d hc

end SerrePositivity.InfinityCategories
