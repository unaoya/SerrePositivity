module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.EquivalenceLifting
public import SerrePositivity.InfinityCategories.Core.JoinEquivalenceFunctor
public import SerrePositivity.InfinityCategories.Core.JoinLifting

/-!
概要：同値持ち上げ射が誘導する slice・coslice の後合成も同値を持ち上げる。
方針：指定された全 join 図式を join による前合成同値に沿って持ち上げる。
規約：元の固定図式と全高次単体を等式で保持する。
使われ方：元の対象上での引き戻しの同期と指定同型の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：slice の後合成は元の同値持ち上げ条件を受け継ぐ。
方針：左因子の join が単射な前合成同値を保つことを使う。
規約：固定図式は任意、両端の quasicategory 性も不要。
使われ方：対象上の比較同型を元の対象を保って持ち上げる。 -/
lemma sliceOverPostcomp_equivalenceLifting {K E B : SSet.{u}}
    (x : K ⟶ E) (p : E ⟶ B) (hp : F1B.EquivalenceLifting p) :
    F1B.EquivalenceLifting (sliceOverPostcomp x p) := by
  intro A T i hi he
  have : Mono i := hi
  have := hp (joinMap i (𝟙 K)) inferInstance (he.joinMap_left K)
  constructor
  intro f g sq
  have hfg : sliceOverUncurry f ≫ p = joinMap i (𝟙 K) ≫ sliceOverUncurry g := by
    rw [← sliceOverUncurry_postcomp, ← sliceOverUncurry_precomp, sq.w]
  let s : CommSq (sliceOverUncurry f) (joinMap i (𝟙 K)) p (sliceOverUncurry g) := ⟨hfg⟩
  have hs : joinInr T K ≫ s.lift = x := by
    calc
      _ = joinInr A K ≫ (joinMap i (𝟙 K) ≫ s.lift) := by
        rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
      _ = x := by rw [s.fac_left]; exact sliceOverUncurry_fixed f
  refine CommSq.HasLift.mk' {
    l := sliceOverCurry s.lift hs
    fac_left := ?_
    fac_right := ?_ }
  · apply sliceOverUncurry_injective x
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry, s.fac_left]
  · apply sliceOverUncurry_injective (x ≫ p)
    rw [sliceOverUncurry_postcomp, sliceOverUncurry_curry, s.fac_right]

/-- 概要：coslice の後合成も元の同値持ち上げ条件を受け継ぐ。
方針：右因子の join が単射な前合成同値を保つことを使う。
規約：元の固定図式を全単体で保持する。
使われ方：固定対象からの全余錐の同型持ち上げ。 -/
lemma sliceUnderPostcomp_equivalenceLifting {K E B : SSet.{u}}
    (x : K ⟶ E) (p : E ⟶ B) (hp : F1B.EquivalenceLifting p) :
    F1B.EquivalenceLifting (sliceUnderPostcomp x p) := by
  intro A T i hi he
  have : Mono i := hi
  have := hp (joinMap (𝟙 K) i) inferInstance (he.joinMap_right K)
  constructor
  intro f g sq
  have hfg : sliceUnderUncurry f ≫ p = joinMap (𝟙 K) i ≫ sliceUnderUncurry g := by
    rw [← sliceUnderUncurry_postcomp, ← sliceUnderUncurry_precomp, sq.w]
  let s : CommSq (sliceUnderUncurry f) (joinMap (𝟙 K) i) p (sliceUnderUncurry g) := ⟨hfg⟩
  have hs : joinInl K T ≫ s.lift = x := by
    calc
      _ = joinInl K A ≫ (joinMap (𝟙 K) i ≫ s.lift) := by
        rw [← Category.assoc, joinInl_joinMap, Category.id_comp]
      _ = x := by rw [s.fac_left]; exact sliceUnderUncurry_fixed f
  refine CommSq.HasLift.mk' {
    l := sliceUnderCurry s.lift hs
    fac_left := ?_
    fac_right := ?_ }
  · apply sliceUnderUncurry_injective x
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry, s.fac_left]
  · apply sliceUnderUncurry_injective (x ≫ p)
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry, s.fac_right]

end SerrePositivity.InfinityCategories.F2.Presentable
