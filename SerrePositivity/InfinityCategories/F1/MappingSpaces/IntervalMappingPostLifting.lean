module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostInclusion
public import SerrePositivity.InfinityCategories.F1B.KanRelativeInternalHomLifting

/-!
概要：相対内部 Hom の持ち上げを、元の両端固定の区間 Hom の後合成へ移す。
方針：境界を定値に固定した比較を作り、同じ持ち上げを境界の fiber へ戻す。
規約：持ち上げる射は任意で、端点の表示は指定した等式で正規化する。
使われ方：分類先の区間 Hom の単射による制限の Kan 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 境界に関する同じ相対内部 Hom の持ち上げは、区間 Hom の後合成を持ち上げる。 -/
lemma hasLiftingProperty_intervalMappingPostOfEq {T U X Y : SSet.{u}}
    (p : X ⟶ Y) (x y : X _⦋0⦌) {x' y' : Y _⦋0⦌}
    (hx : p.app _ x = x') (hy : p.app _ y = y')
    (r : internalHom.PullbackObjObj (boundary 1).ι p) (j : T ⟶ U)
    [HasLiftingProperty j r.π] :
    HasLiftingProperty j (intervalMappingPostOfEq p x y hx hy) := by
  constructor
  intro a b sq
  let ιX := vertexFiberι ((pre (boundary 1).ι).app X)
    (functorVertex (intervalMappingBoundary x y))
  let ιY := vertexFiberι ((pre (boundary 1).ι).app Y)
    (functorVertex (intervalMappingBoundary x' y'))
  have hπfst : r.π ≫ r.fst = (pre (boundary 1).ι).app X := r.π_fst
  have hπsnd : r.π ≫ r.snd = (ihom (Δ[1] : SSet.{u})).map p := r.π_snd
  have hb : intervalMappingBoundary x y ≫ p = intervalMappingBoundary x' y' := by
    rw [intervalMappingBoundary_post, hx, hy]
  let V : U ⟶ r.pt := r.isPullback.lift
    (SSet.const (functorVertex (intervalMappingBoundary x y))) (b ≫ ιY) (by
      change SSet.const (functorVertex (intervalMappingBoundary x y)) ≫
        (ihom (boundary 1 : SSet.{u})).map p = (b ≫ ιY) ≫ (pre (boundary 1).ι).app Y
      dsimp only [ιY]
      rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.const_comp]
      change SSet.const (functorVertex (intervalMappingBoundary x y ≫ p)) = _
      rw [hb])
  have hVfst : V ≫ r.fst = SSet.const (functorVertex (intervalMappingBoundary x y)) :=
    r.isPullback.lift_fst _ _ _
  have hVsnd : V ≫ r.snd = b ≫ ιY := r.isPullback.lift_snd _ _ _
  let sq' : CommSq (a ≫ ιX) j r.π V := by
    constructor
    apply r.hom_ext
    · simp only [Category.assoc, hπfst, hVfst]
      dsimp only [ιX]
      rw [vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
    · simp only [Category.assoc, hπsnd, hVsnd]
      exact (intervalMappingPostOfEq_ι p x y hx hy a).symm.trans
        (by rw [sq.w, Category.assoc])
  have hbase : sq'.lift ≫ (pre (boundary 1).ι).app X =
      SSet.const (functorVertex (intervalMappingBoundary x y)) := by
    rw [← hπfst, ← Category.assoc, sq'.fac_right, hVfst]
  let W := vertexFiberLift _ _ sq'.lift hbase
  refine CommSq.HasLift.mk' { l := W, fac_left := ?_, fac_right := ?_ }
  · apply vertexFiber_hom_ext ((pre (boundary 1).ι).app X)
      (functorVertex (intervalMappingBoundary x y))
    rw [Category.assoc, vertexFiberLift_ι]
    exact sq'.fac_left
  · apply vertexFiber_hom_ext ((pre (boundary 1).ι).app Y)
      (functorVertex (intervalMappingBoundary x' y'))
    rw [intervalMappingPostOfEq_ι, vertexFiberLift_ι]
    change sq'.lift ≫ (ihom (Δ[1] : SSet.{u})).map p = b ≫ ιY
    rw [← hπsnd, ← Category.assoc, sq'.fac_right, hVsnd]

/-- 同値を右に持ち上げる射の、同じ区間 Hom の後合成も同値を右に持ち上げる。 -/
lemma kanEquivalenceLifting_intervalMappingPostOfEq {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : F1B.KanEquivalenceLifting p) (x y : X _⦋0⦌) {x' y' : Y _⦋0⦌}
    (hx : p.app _ x = x') (hy : p.app _ y = y') :
    F1B.KanEquivalenceLifting (intervalMappingPostOfEq p x y hx hy) := by
  let r := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom (boundary 1).ι p
  intro T U j hj he
  have := hp.relativeInternalHom (boundary 1).ι r j hj he
  exact hasLiftingProperty_intervalMappingPostOfEq p x y hx hy r j

end SerrePositivity.InfinityCategories
