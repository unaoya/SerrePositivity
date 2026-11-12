module
public import SerrePositivity.KST.SConstruction.EquivalenceFamilyPathRecovery

/-! # 指定境界と比較円柱を保持する同値に沿う族の回収
概要：同値の先の全パラメータ族を、元の境界と境界定数の比較円柱を持つ族に戻す。
方針：同値の path 置換の境界固定の持ち上げを元の始域と path に射影する。
規約：回収後の像と元の族の厳密一致は仮定せず、実際の比較ホモトピーを保持する。
使われ方：固定端点の coherent な区間族を native な写像空間へ相対的に回収する。
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

/-- 元の指定境界を持つ族と、境界で定数な元の族への実比較円柱。 -/
structure RelativeEquivalenceFamilyData {E B T U : SSet.{u}} (q : E ⟶ B)
    (j : T ⟶ U) (a : T ⟶ E) (b : U ⟶ B) where
  /-- 元の同値の始域に回収した全パラメータ族。 -/
  family : U ⟶ E
  /-- 回収した族の境界は元の指定族そのもの。 -/
  boundary : j ≫ family = a
  /-- 回収した族の像から元の先の族への実比較。 -/
  comparison : SSet.Homotopy (family ≫ q) b
  /-- 比較は元の境界の像で全時刻にわたり固定する。 -/
  comparison_boundary : (j ▷ (Δ[1] : SSet.{u})) ≫ comparison.h =
    fst T (Δ[1] : SSet.{u}) ≫ a ≫ q

/-- 同値の先の族を元の指定境界のまま回収し、境界定数の実比較円柱も与える。 -/
def relativeEquivalenceFamilyRecovery {E B T U : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (q : E ⟶ B) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence q)
    (j : T ⟶ U) [Mono j] (a : T ⟶ E) (b : U ⟶ B)
    (h : a ≫ q = j ≫ b) : RelativeEquivalenceFamilyData q j a b := by
  let L := relativeEquivalenceFamilyPathLift q hq j a b h
  let g := L.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection q
  let H := equivalenceFamilyPathHomotopy q L.val
  have hg : j ≫ g = a := by
    rw [show j ≫ g = (j ≫ L.val) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection q from
      (Category.assoc _ _ _).symm, L.property.1, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection, Category.comp_id]
  let V : SSet.Homotopy (g ≫ q) b :=
    { h := H.h, h₀ := H.h₀, h₁ := H.h₁.trans L.property.2, rel := H.rel }
  refine ⟨g, hg, V, ?_⟩
  change (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = _
  rw [← equivalenceFamilyPathHomotopy_precomp]
  have he := congrArg (fun m : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement q =>
    (equivalenceFamilyPathHomotopy q m).h) L.property.1
  exact he.trans (equivalenceFamilyPathHomotopy_section_pre q a)

end SerrePositivity.KST.SConstruction
