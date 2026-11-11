module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! # 同値の path 置換による境界固定の族の回収
概要：同値の像にある族を、指定した境界を厳密に保つ元の族と実比較円柱へ戻す。
方針：同値の path 置換の全単射 RLP で持ち上げ、元の射影と普遍 path を評価する。
規約：比較円柱を破棄せず、境界では定値 path を固定する。
使われ方：coherent nerve の固定端点の区間族を元の豊穣 Hom の族へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- path 置換の任意の族から得る、元の像と元の終点を結ぶ実比較円柱。 -/
def equivalenceFamilyPathHomotopy {E B A : SSet.{u}} (q : E ⟶ B)
    (l : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement q) : SSet.Homotopy
      (l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection q ≫ q)
      (l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap q) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathHomotopy B)
    (l ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) q)
  refine { h := H.h, h₀ := H.h₀.trans ?_, h₁ := H.h₁, rel := H.rel }
  rw [Category.assoc, pullback.condition]
  rfl

/-- 定値 path の切断では、元の比較円柱は全次数で定数になる。 -/
lemma equivalenceFamilyPathHomotopy_section {E B : SSet.{u}} (q : E ⟶ B) :
    (equivalenceFamilyPathHomotopy q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection q)).h =
      fst E (Δ[1] : SSet.{u}) ≫ q := by
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection q ≫
    pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) q) ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathHomotopy B).h) = _
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection q ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) q = q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl B :=
    pullback.lift_fst _ _ _
  rw [hs, comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathHomotopy_refl]
  exact whiskerRight_fst q (Δ[1] : SSet.{u})

/-- 元の普遍比較円柱はパラメータの前合成を厳密に保持する。 -/
lemma equivalenceFamilyPathHomotopy_precomp {E B A T : SSet.{u}} (q : E ⟶ B)
    (l : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement q) (i : T ⟶ A) :
    (equivalenceFamilyPathHomotopy q (i ≫ l)).h =
      (i ▷ (Δ[1] : SSet.{u})) ≫ (equivalenceFamilyPathHomotopy q l).h := by
  change (((i ≫ l) ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) q) ▷ (Δ[1] : SSet.{u})) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathHomotopy B).h = _
  rw [Category.assoc, comp_whiskerRight_assoc]
  rfl

/-- 元の族からの定値 path の比較円柱は、全パラメータで厳密に定数。 -/
lemma equivalenceFamilyPathHomotopy_section_pre {E B T : SSet.{u}}
    (q : E ⟶ B) (a : T ⟶ E) :
    (equivalenceFamilyPathHomotopy q (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection q)).h =
      fst T (Δ[1] : SSet.{u}) ≫ a ≫ q := by
  rw [equivalenceFamilyPathHomotopy_precomp, equivalenceFamilyPathHomotopy_section]
  exact whiskerRight_fst_assoc a _ q

/-- 任意の単射パラメータ境界を厳密に固定する、同値の path 置換への持ち上げ。 -/
def relativeEquivalenceFamilyPathLift {E B T U : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence q)
    (j : T ⟶ U) [Mono j] (a : T ⟶ E) (b : U ⟶ B)
    (h : a ≫ q = j ≫ b) :
    {l : U ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement q //
      j ≫ l = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection q ∧
      l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap q = b} := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap q) :=
    hq.equivalencePathReplacementMap_trivialKanFibration
  let : HasLiftingProperty j (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap q) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem j inferInstance
  let sq : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection q) j
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap q) b := ⟨by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_map, h]⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end SerrePositivity.KST.SConstruction
