module

public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：錐の後合成と trivial Kan fibration による極限の保存・反映。
方針：slice の後合成の境界持ち上げを join に移し、slice の同値に終対象の判定を適用する。
規約：任意の図式の単体集合 K を扱う。
使われ方：HTT §1.2.13、Kerodon §7.1、Theorem 4.8.4.1 の準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：錐を単体集合の射で後合成する。
方針：錐の射と固定図式を同じ射で写す。
規約：像の図式は p≫f。
使われ方：HTT §1.2.13、Kerodon §7.1 の極限の保存。 -/
def mapJoinCone {K X Y : SSet.{u}} (f : X ⟶ Y) {p : K ⟶ X} (c : JoinCone p) :
    JoinCone (p ≫ f) := ⟨c.val ≫ f, by rw [← Category.assoc, c.property]⟩

/-- 概要：錐の後合成は slice の後合成の零次成分。
方針：両定義を展開する。
規約：零単体と錐の部分型を同じ型として読む。
使われ方：HTT §1.2.13、slice の終対象性による極限の判定。 -/
lemma mapJoinCone_eq_sliceOverPostcomp {K X Y : SSet.{u}} (f : X ⟶ Y)
    {p : K ⟶ X} (c : JoinCone p) :
    mapJoinCone f c = (sliceOverPostcomp p f).app (Opposite.op ⦋0⦌) c := rfl

/-- 概要：像の錐の頂点は元の頂点の像。
方針：左包含による制限と Yoneda の後合成の自然性を使う。
規約：図式の単体集合 K は任意。
使われ方：HTT §1.2.13 の極限対象の像。 -/
lemma mapJoinCone_vertex {K X Y : SSet.{u}} (f : X ⟶ Y) {p : K ⟶ X} (c : JoinCone p) :
    (mapJoinCone f c).vertex = f.app (Opposite.op ⦋0⦌) c.vertex := by
  change SSet.yonedaEquiv (joinInl Δ[0] K ≫ (c.val ≫ f)) = _
  rw [← Category.assoc, SSet.yonedaEquiv_comp]
  rfl

/-- 概要：slice の後合成は trivial Kan fibration 性を保つ。
方針：境界の持ち上げを、join の単射に沿う元の射の持ち上げへ移す。
規約：固定図式の持ち上げ p は与えられている。
使われ方：HTT §1.2.13、Kerodon §7.1 の極限の保存と反映。 -/
@[kerodon 01NT]
instance trivialKanFibration_sliceOverPostcomp {K E B : SSet.{u}} (p : K ⟶ E) (q : E ⟶ B)
    [TrivialKanFibration q] : TrivialKanFibration (sliceOverPostcomp p q) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  let i := joinMap (boundary n).ι (𝟙 K)
  have hm : Mono i := joinMap_mono _ _
  have := TrivialKanFibration.mem (p := q) i hm
  have hw := congrArg (fun F ↦ sliceOverUncurry F) sq.w
  rw [sliceOverUncurry_postcomp, sliceOverUncurry_precomp] at hw
  have s : CommSq (sliceOverUncurry a) i q (sliceOverUncurry b) := ⟨hw⟩
  have hK : joinInr (Δ[n] : SSet.{u}) K ≫ s.lift = p := by
    have h := congrArg (fun F ↦ joinInr (boundary n : SSet.{u}) K ≫ F) s.fac_left
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp] at h
    exact h.trans (sliceOverUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceOverCurry s.lift hK, fac_left := ?_, fac_right := ?_ }
  · apply sliceOverUncurry_injective p
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry]
    exact s.fac_left
  · apply sliceOverUncurry_injective (p ≫ q)
    rw [sliceOverUncurry_postcomp, sliceOverUncurry_curry]
    exact s.fac_right

/-- 概要：trivial Kan fibration は任意の図式の極限錐を保存・反映する。
方針：slice の後合成の明示的な同値に終対象性の同値不変性を適用する。
規約：これは一般の同値ではなく trivial Kan fibration の場合の定理。
使われ方：HTT §1.2.13、Kerodon §7.1、Theorem 4.8.4.1 の還元。 -/
lemma isLimitCone_iff_mapJoinCone_of_trivialKanFibration {K E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) [TrivialKanFibration q]
    {p : K ⟶ E} (c : JoinCone p) : IsLimitCone c ↔ IsLimitCone (mapJoinCone q c) :=
  (qCatEquivalenceOfTrivialKanFibration (sliceOverPostcomp p q)).isTerminalVertex_iff c

end SerrePositivity.InfinityCategories
