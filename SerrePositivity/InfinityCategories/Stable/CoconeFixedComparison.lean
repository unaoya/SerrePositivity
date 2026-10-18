module
public import SerrePositivity.InfinityCategories.Stable.CoconeFamily
public import SerrePositivity.InfinityCategories.Core.FixedDiagramPrecomposition
public import SerrePositivity.InfinityCategories.Core.FatJoinGeneralComparison
public import SerrePositivity.InfinityCategories.Core.FatJoinComparisonEpi

/-! # 左図式を固定した fat join 比較

概要：余錐の基底図式を固定した関手圏でも fat join 比較は同値を誘導する。
方針：既証明の普遍的前合成同値を、左包含の上の厳密な fiber に制限する。
規約：Core の右図式を固定した比較の双対。使われ方：余錐の族と coslice の比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：fat join の左包含は単射である。
方針：join への比較と合成すると単射な join の左包含になる。
規約：両因子は任意。使われ方：固定図式上の比較の fiber を取る条件。 -/
instance stable_fatJoinInl_mono (A B : SSet.{u}) : Mono (fatJoinInl A B) := by
  have : Mono (fatJoinInl A B ≫ fatJoinComparison A B) := by
    rw [fatJoinInl_comparison]
    infer_instance
  exact mono_of_mono (fatJoinInl A B) (fatJoinComparison A B)

/-- 概要：左因子の図式を固定した関手圏で fat join 比較は同値を誘導する。
方針：比較射はエピな普遍的前合成同値なので、固定図式上の fiber に制限する。
規約：値域 X は quasicategory。使われ方：coslice の関手圏による模型との比較。 -/
lemma isQCatEquivalence_fatJoinComparison_fixedLeftDiagram
    (K A X : SSet.{u}) [Quasicategory X] (p : K ⟶ X) :
    IsQCatEquivalence (fixedDiagramPre (joinInl K A) (fatJoinInl K A)
      (fatJoinComparison K A) (fatJoinInl_comparison K A) p) := by
  apply isQCatEquivalence_fixedDiagramPre
  exact isPrecompositionEquivalence_fatJoinComparison K A

end SerrePositivity.InfinityCategories
