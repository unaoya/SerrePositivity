module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：quasicategory の同値による任意の極限錐の保存と反映。
方針：可逆 path 置換の二射影を trivial Kan fibration にし、厳密な切断を介して還元する。
規約：図式の単体集合は任意、同値は A3a の逆データを持つもの。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1）、Theorem 4.8.4.1（Tag 01JX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：同値の path 置換の終点射は trivial Kan fibration。
方針：同値の充満忠実性と本質的全射性を path 置換へ移す。
規約：元の関手に inner fibration 性を要求しない。
使われ方：Kerodon Theorem 4.8.4.1（Tag 01JX） の二つの trivial fibration による表現。 -/
lemma IsQCatEquivalence.equivalencePathReplacementMap_trivialKanFibration {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f) :=
  he.isFullyFaithful.equivalencePathReplacementMap.trivialKanFibration_of_surjective
    he.choose.isEssentiallySurjective.equivalencePathReplacementMap_surjective

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsQCatEquivalence (equivalencePathReplacementMap_trivialKanFibration)


/-- 概要：等しい図式上の同じ錐の極限性は一致する。
方針：図式の等式で置換し、錐の部分型の外延性を使う。
規約：図式の等式と錐の射の等式の両方を仮定する。
使われ方：HTT §1.2.13 の錐の厳密な合成の整合。 -/
lemma isLimitCone_iff_of_diagram_eq {K X : SSet.{u}} {p q : K ⟶ X}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q} (hp : p = q) (hc : c.val = d.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d := by
  subst q
  have h : c = d := Subtype.ext hc
  rw [h]

/-- 概要：trivial Kan fibration の厳密な切断は任意の極限錐を保存・反映する。
方針：射影による極限錐の保存・反映と切断の等式を使う。
規約：射影と切断の両端は quasicategory。
使われ方：HTT §1.2.13 の同値による極限不変性への還元。 -/
lemma isLimitCone_iff_mapJoinCone_of_section {K X E : SSet.{u}}
    [Quasicategory X] [Quasicategory E] (q : E ⟶ X) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q]
    (s : X ⟶ E) (hs : s ≫ q = 𝟙 X) {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone s c) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.isLimitCone_iff_mapJoinCone_of_trivialKanFibration q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone s c)
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone s c)) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c :=
    isLimitCone_iff_of_diagram_eq
      (by rw [Category.assoc, hs, Category.comp_id])
      (by change (c.val ≫ s) ≫ q = c.val; rw [Category.assoc, hs, Category.comp_id])
  exact hb.symm.trans h.symm

/-- 概要：quasicategory の同値は任意の図式の極限錐を保存・反映する。
方針：path 置換への切断と終点射に分解し、各段階で極限錐を検出する。
規約：図式の単体集合 K は任意。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の同値による極限不変性。 -/
@[kerodon 02JZ]
lemma IsQCatEquivalence.isLimitCone_iff {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f)
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone f c) := by
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection f
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f
  haveI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q := he.equivalencePathReplacementMap_trivialKanFibration
  have h₀ := isLimitCone_iff_mapJoinCone_of_section (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection f)
    s (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection f) c
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.isLimitCone_iff_mapJoinCone_of_trivialKanFibration q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone s c)
  have h := h₀.trans h₁
  apply h.trans
  apply isLimitCone_iff_of_diagram_eq
  · change (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f = p ≫ f
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_map]
  · change (c.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection f) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f = c.val ≫ f
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_map]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsQCatEquivalence (isLimitCone_iff)


/-- 概要：明示的な同値は任意の極限錐を保存・反映する。
方針：逆データから同値性を取り出して一般形を適用する。
規約：像の図式は p≫e.hom。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の利用側 API。 -/
@[kerodon 02JZ]
lemma QCatEquivalence.isLimitCone_iff {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y)
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone e.hom c) :=
  e.isQCatEquivalence.isLimitCone_iff c

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.QCatEquivalence (isLimitCone_iff)


end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
