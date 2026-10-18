module

public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Core.EquivalenceLimits

/-!
概要：quasicategory の同値による任意の極限錐の保存と反映。
方針：可逆 path 置換の二射影を trivial Kan fibration にし、厳密な切断を介して還元する。
規約：図式の単体集合は任意、同値は A3a の逆データを持つもの。
使われ方：HTT §1.2.13、Kerodon §7.1、Theorem 4.8.4.1。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：同値の path 置換の終点射は trivial Kan fibration。
方針：同値の充満忠実性と本質的全射性を path 置換へ移す。
規約：元の関手に inner fibration 性を要求しない。
使われ方：Kerodon Theorem 4.8.4.1 の二つの trivial fibration による表現。 -/
lemma IsQCatEquivalence.equivalencePathReplacementMap_trivialKanFibration {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (he : IsQCatEquivalence f) :
    TrivialKanFibration (equivalencePathReplacementMap f) :=
  he.isFullyFaithful.equivalencePathReplacementMap.trivialKanFibration_of_surjective
    he.choose.isEssentiallySurjective.equivalencePathReplacementMap_surjective

/-- 概要：等しい図式上の同じ錐の極限性は一致する。
方針：図式の等式で置換し、錐の部分型の外延性を使う。
規約：図式の等式と錐の射の等式の両方を仮定する。
使われ方：HTT §1.2.13 の錐の厳密な合成の整合。 -/
lemma isLimitCone_iff_of_diagram_eq {K X : SSet.{u}} {p q : K ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (hp : p = q) (hc : c.val = d.val) :
    IsLimitCone c ↔ IsLimitCone d := by
  subst q
  have h : c = d := Subtype.ext hc
  rw [h]

/-- 概要：trivial Kan fibration の厳密な切断は任意の極限錐を保存・反映する。
方針：射影による極限錐の保存・反映と切断の等式を使う。
規約：射影と切断の両端は quasicategory。
使われ方：HTT §1.2.13 の同値による極限不変性への還元。 -/
lemma isLimitCone_iff_mapJoinCone_of_section {K X E : SSet.{u}}
    [Quasicategory X] [Quasicategory E] (q : E ⟶ X) [TrivialKanFibration q]
    (s : X ⟶ E) (hs : s ≫ q = 𝟙 X) {p : K ⟶ X} (c : JoinCone p) :
    IsLimitCone c ↔ IsLimitCone (mapJoinCone s c) := by
  have h := isLimitCone_iff_mapJoinCone_of_trivialKanFibration q (mapJoinCone s c)
  have hb : IsLimitCone (mapJoinCone q (mapJoinCone s c)) ↔ IsLimitCone c :=
    isLimitCone_iff_of_diagram_eq
      (by rw [Category.assoc, hs, Category.comp_id])
      (by change (c.val ≫ s) ≫ q = c.val; rw [Category.assoc, hs, Category.comp_id])
  exact hb.symm.trans h.symm

/-- 概要：quasicategory の同値は任意の図式の極限錐を保存・反映する。
方針：path 置換への切断と終点射に分解し、各段階で極限錐を検出する。
規約：図式の単体集合 K は任意。
使われ方：HTT §1.2.13、Kerodon §7.1 の同値による極限不変性。 -/
lemma IsQCatEquivalence.isLimitCone_iff {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (he : IsQCatEquivalence f)
    {p : K ⟶ X} (c : JoinCone p) : IsLimitCone c ↔ IsLimitCone (mapJoinCone f c) := by
  let s := equivalencePathReplacementSection f
  let q := equivalencePathReplacementMap f
  haveI : TrivialKanFibration q := he.equivalencePathReplacementMap_trivialKanFibration
  have h₀ := isLimitCone_iff_mapJoinCone_of_section (equivalencePathReplacementProjection f)
    s (equivalencePathReplacementSection_projection f) c
  have h₁ := isLimitCone_iff_mapJoinCone_of_trivialKanFibration q (mapJoinCone s c)
  have h := h₀.trans h₁
  apply h.trans
  apply isLimitCone_iff_of_diagram_eq
  · change (p ≫ equivalencePathReplacementSection f) ≫ equivalencePathReplacementMap f = p ≫ f
    rw [Category.assoc, equivalencePathReplacementSection_map]
  · change (c.val ≫ equivalencePathReplacementSection f) ≫
      equivalencePathReplacementMap f = c.val ≫ f
    rw [Category.assoc, equivalencePathReplacementSection_map]

/-- 概要：明示的な同値は任意の極限錐を保存・反映する。
方針：逆データから同値性を取り出して一般形を適用する。
規約：像の図式は p≫e.hom。
使われ方：HTT §1.2.13、Kerodon §7.1 の利用側 API。 -/
lemma QCatEquivalence.isLimitCone_iff {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y)
    {p : K ⟶ X} (c : JoinCone p) : IsLimitCone c ↔ IsLimitCone (mapJoinCone e.hom c) :=
  e.isQCatEquivalence.isLimitCone_iff c

end SerrePositivity.InfinityCategories
