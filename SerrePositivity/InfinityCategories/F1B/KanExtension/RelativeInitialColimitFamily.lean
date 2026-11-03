module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeColimit
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorRelativeInitial
public import SerrePositivity.InfinityCategories.F1.ColimitRelativeBoundary
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationCocone

/-!
概要：点ごとに相対始対象である族の余極限全余錐は、全族の後合成について相対始対象。
方針：点ごとの境界充填と余極限の境界充填を合成し、像の余極限条件を消去する。
規約：元の図式とその全余錐、像の同じ全余錐を保持する。
使われ方：余極限同士の交換で、完成した全族の普遍性を頂点へ戻す準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 相対始対象性の合成から、像での相対始対象性を消去する。 -/
lemma KanRelativeInitialVertex.cancel_right {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    {U : X ⟶ Y} {V : Y ⟶ Z} {x : X _⦋0⦌}
    (hUV : KanRelativeInitialVertex (U ≫ V) x)
    (hV : KanRelativeInitialVertex V (U.app (Opposite.op ⦋0⦌) x)) :
    KanRelativeInitialVertex U x := by
  intro y
  have h := hUV y
  rw [pinchedHomMap_comp] at h
  exact (hV _).cancel_right h

set_option maxHeartbeats 800000 in
-- 全内部 Hom の型推論で固定図式の同一視を保持するため上限を広げる。
/-- 点ごとの相対始対象族の余極限とその像が余極限なら、全余錐自体は後合成の相対始対象。 -/
lemma relativeInitial_colimitCoconeFamily {I X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y) (p : I ⟶ X)
    (hp : ∀ i, InitialBoundaryLifting U (p.app (Opposite.op ⦋0⦌) i))
    (c : JoinCocone p) (hc : IsColimitCone c)
    (hUc : IsColimitCone (mapJoinCocone U c)) :
    KanRelativeInitialVertex ((ihom (join I (Δ[0] : SSet.{u}))).map U)
      (functorVertex c.val) := by
  have ha := kanRelativeInitialVertex_of_initialBoundary (coconeRestriction I X)
    (functorVertex c.val) hc.initialBoundaryLifting
  have hb : KanRelativeInitialVertex ((ihom I).map U)
      ((coconeRestriction I X).app (Opposite.op ⦋0⦌) (functorVertex c.val)) := by
    change KanRelativeInitialVertex ((ihom I).map U)
      (functorVertex (joinInl I (Δ[0] : SSet.{u}) ≫ c.val))
    rw [c.property]
    exact kanRelativeInitialVertex_of_initialBoundary _ _
      (initialBoundaryLifting_ihom_of_pointwise U p hp)
  have hab := ha.comp hb
  have he : coconeRestriction I X ≫ (ihom I).map U =
      (ihom (join I (Δ[0] : SSet.{u}))).map U ≫ coconeRestriction I Y :=
    (pre (joinInl I (Δ[0] : SSet.{u}))).naturality U
  rw [he] at hab
  apply hab.cancel_right
  exact kanRelativeInitialVertex_of_initialBoundary _ _ hUc.initialBoundaryLifting

end SerrePositivity.InfinityCategories.F1B
