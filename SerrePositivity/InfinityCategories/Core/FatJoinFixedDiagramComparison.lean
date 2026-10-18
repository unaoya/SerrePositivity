module

public import SerrePositivity.InfinityCategories.Core.FatJoinComparisonEpi
public import SerrePositivity.InfinityCategories.Core.PrecompositionMonomorphism
public import SerrePositivity.InfinityCategories.Core.PrecompositionFiberEquivalence

/-!
概要：図式を固定した関手圏における fat join と join の比較。
方針：比較射のエピ性と普遍的同値性を、前合成の fiber の同値へ移す。
規約：右因子上の図式を厳密に固定する。
使われ方：Kerodon §4.6.4・4.6.6 の slice の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：fat join の右包含は単射。
方針：一端の単射の pushout を使う。
規約：両因子は任意。
使われ方：Kerodon §4.6.4 の固定図式への射影。 -/
instance fatJoinInr_mono (A B : SSet.{u}) : Mono (fatJoinInr A B) := by
  exact Adhesive.mono_of_isPushout_of_mono_left
    (IsPushout.of_hasPushout (fatJoinStageEnd A B) (snd A B))

/-- 概要：右因子上の図式を固定した関手圏でも fat join 比較は同値を誘導する。
方針：普遍的比較の前合成は単射な同値であり、固定図式上の fiber へ制限する。
規約：値域 X は quasicategory、A と K は任意。
使われ方：Kerodon Proposition 4.6.4.19 と Proposition 4.6.6.7 の相対的な比較。 -/
lemma isQCatEquivalence_fatJoinComparison_fixedDiagram
    (A K X : SSet.{u}) [Quasicategory X] (p : K ⟶ X) :
    IsQCatEquivalence (vertexFiberMap
      ((pre (joinInr A K)).app X) ((pre (fatJoinInr A K)).app X)
      ((pre (fatJoinComparison A K)).app X)
      (by rw [← NatTrans.comp_app, ← pre_map, fatJoinInr_comparison]) (functorVertex p)) := by
  apply isQCatEquivalence_vertexFiberMap_pre
  exact isPrecompositionEquivalence_fatJoinComparison A K X

end SerrePositivity.InfinityCategories
