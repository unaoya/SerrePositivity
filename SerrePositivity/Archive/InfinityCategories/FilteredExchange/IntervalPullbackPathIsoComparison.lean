module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementPathIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IntervalPullbackPathHomotopy
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.HomotopyIsoTransport

/-!
概要：置換の元の path の制限と引き戻しの元の全 path の指定同型の一致。
方針：同じ全円柱を保持し終点だけ引き戻し条件で輸送する。
規約：指定値を保持。使われ方：区間錐と具体的な path の最終整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {X Y Z : SSet.{u}} [KanComplex Y] (f : X ⟶ Y) (g : Z ⟶ Y)

omit [KanComplex Y] in
/-- 概要：置換の元の円柱を第一射影で制限すると元の引き戻し path 円柱。
方針：交換と uncurry の自然性。規約：全時刻の式。使われ方：指定同型の比較。 -/
lemma intervalPullbackPathHomotopy_precomp :
    (functorHomotopyPrecomp (intervalReplacementCanonicalPathHomotopy f)
      (pullback.fst (intervalReplacementEndpoint f) g)).h =
        (intervalPullbackPathHomotopy f g).h := by
  let a := pullback.fst (intervalReplacementEndpoint f) g
  have hswap : (a ▷ (Δ[1] : SSet.{u})) ≫
      (β_ (intervalReplacement f) (Δ[1] : SSet.{u})).hom =
    (β_ (intervalPullback f g) (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ a) := rfl
  change (a ▷ (Δ[1] : SSet.{u})) ≫ (β_ (intervalReplacement f) (Δ[1] : SSet.{u})).hom ≫
      uncurry (pullback.fst ((intervalEndpointNatTrans 0).app Y) f) =
    (β_ (intervalPullback f g) (Δ[1] : SSet.{u})).hom ≫
      uncurry (a ≫ pullback.fst ((intervalEndpointNatTrans 0).app Y) f)
  rw [← Category.assoc, hswap, Category.assoc, ← uncurry_natural_left]

/-- 概要：元の引き戻し path の指定同型は置換 path の制限と元の終点等式の合成。
方針：全円柱の一致と終点の等式による輸送。
規約：元の指定同型の値を保持。使われ方：native 可換性との最終照合。 -/
lemma intervalPullbackPathIso_comparison :
    (intervalReplacementPathIso f).precomp (pullback.fst (intervalReplacementEndpoint f) g) ≪≫
      functorEqIso (pullback.condition (f := intervalReplacementEndpoint f) (g := g)) =
        intervalPullbackPathIso f g := by
  rw [← functorIsoOfEq_target_trans]
  apply functorIsoOfEq_of_homotopy_h_eq
    (functorHomotopyPrecomp (intervalReplacementCanonicalPathHomotopy f)
      (pullback.fst (intervalReplacementEndpoint f) g)) (intervalPullbackPathHomotopy f g)
  · rw [functorIso_precomp_hom, intervalReplacementPathIso_hom]
    exact (functorHomotopyPrecomp_hom (intervalReplacementCanonicalPathHomotopy f)
      (pullback.fst (intervalReplacementEndpoint f) g)).symm
  · exact intervalPullbackPathIso_hom f g
  · exact intervalPullbackPathHomotopy_precomp f g

end SerrePositivity.InfinityCategories.F2
