module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ConeFamilyApex

/-!
概要：固定図式上の錐の関手圏での任意の比較射の頂点を、元の標準極限比較と照合する。
方針：終対象への射の一意性と、既存の全頂点射影の可換式を使う。
規約：HTT §1.2.13、Kerodon Example 4.6.6.8（Tag 04J5）の既存比較の計算法則。
使われ方：S8 の指定右Kan輸送の比較を、元の標準極限頂点比較へ戻す。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 既存のslice比較と頂点射影の可換式を同じ錐で評価した頂点等式。 -/
lemma sliceConeFamilyMap_apex_vertex {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) :
    (coneFamilyApex p).app _ ((sliceConeFamilyMap p).app _ c) = c.vertex :=
  congrArg (fun f => f.app (Opposite.op ⦋0⦌) c) (sliceConeFamilyMap_apex p)

/-- 固定図式上の錐の関手圏の比較射は、元の標準極限比較と同じ頂点射を持つ。 -/
lemma limitVertexIso_coneFamily_projection {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c d : JoinCone p) (hc : IsLimitCone c) (hd : IsLimitCone d)
    (m : (HomotopyCategory.mk ((sliceConeFamilyMap p).app _ c) :
      hoFunctor.obj (coneFamily p)) ⟶ HomotopyCategory.mk ((sliceConeFamilyMap p).app _ d)) :
    (hoFunctor.map (coneFamilyApex p)).toFunctor.map m ≫
      eqToHom (congrArg HomotopyCategory.mk (sliceConeFamilyMap_apex_vertex d)) =
    eqToHom (congrArg HomotopyCategory.mk (sliceConeFamilyMap_apex_vertex c)) ≫
      (limitVertexIso c d hc hd).hom := by
  have hd' : IsTerminalVertex ((sliceConeFamilyMap p).app _ d) := by
    rw [sliceConeFamilyMap_app_zero]
    exact (isLimitCone_iff_isTerminalVertex_coneFamily d).mp hd
  have hm : m = (hoFunctor.map (sliceConeFamilyMap p)).toFunctor.map
      (limitConeIso c d hc hd).hom := hd'.isTerminalHo.hom_ext _ _
  rw [hm]
  have hp : (hoFunctor.map (sliceConeFamilyMap p)).toFunctor ⋙
      (hoFunctor.map (coneFamilyApex p)).toFunctor =
        (hoFunctor.map (sliceOverProjection p)).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← Functor.map_comp, sliceConeFamilyMap_apex]
  have h := (eqToHom hp).naturality (limitConeIso c d hc hd).hom
  simp only [eqToHom_app] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
