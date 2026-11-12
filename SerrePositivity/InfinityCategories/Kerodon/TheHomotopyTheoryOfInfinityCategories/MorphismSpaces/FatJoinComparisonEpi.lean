module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinGeneralComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinCurryHomExt

/-!
概要：任意の二つの単体集合の fat join 比較のエピ性。
方針：標準単体での切断と左右二回の curry の外延性を使う。
規約：両因子の非空性・有限性は要求しない。
使われ方：Kerodon Notation 4.6.2.3（Tag 01HR） の比較の全射性と slice の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：標準単体の fat join 比較はエピ射。
方針：既に構成した切断で左からの合成を消す。
規約：二つの次元は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較のエピ性。 -/
instance fatJoinComparison_stdSimplex_epi (n m : ℕ) :
    Epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison (Δ[n] : SSet.{u}) Δ[m]) := by
  constructor
  intro X f g h
  have he := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdSection n m ≫ z) h
  simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStdSection_comparison, Category.id_comp] using he

/-- 概要：左因子が標準単体なら fat join 比較は任意の右因子でエピ射。
方針：右因子の標準単体で比較して標準単体の切断へ戻す。
規約：右因子の非空性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の一般の比較への第一段階。 -/
instance fatJoinComparison_stdSimplex_left_epi (n : ℕ) (B : SSet.{u}) :
    Epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison (Δ[n] : SSet.{u}) B) := by
  constructor
  intro X f g h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_right_hom_ext
  · simpa only [reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_comparison] using
      congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl (Δ[n] : SSet.{u}) B ≫ z) h
  · intro m b
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison (Δ[n] : SSet.{u}) Δ[m])).1
    simpa only [reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison_naturality] using
      congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap (𝟙 (Δ[n] : SSet.{u})) b ≫ z) h

/-- 概要：任意の二つの単体集合の fat join 比較はエピ射。
方針：左因子の全標準単体で比較し、片側が標準単体のエピ性を使う。
規約：両因子の非空性・有限性・quasicategory 性は不要。
使われ方：Kerodon Notation 4.6.2.3（Tag 01HR） の比較の全射性。 -/
instance (priority := 100) fatJoinComparison_epi (A B : SSet.{u}) : Epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison A B) := by
  constructor
  intro X f g h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_left_hom_ext
  · simpa only [reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_comparison] using
      congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B ≫ z) h
  · intro n a
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison (Δ[n] : SSet.{u}) B)).1
    simpa only [reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison_naturality] using
      congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap a (𝟙 B) ≫ z) h

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
