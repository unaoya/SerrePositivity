module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationInitialHomNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingPiZero
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ColimitExistenceTransfer
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitReindex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanCoconeMappingSwap

/-! # 余錐空間の Hom 表示と形状の制限

概要：余極限を保つ形状の制限は余錐空間の連結成分の Hom 表示と可換。
方針：coslice の制限を同じ底上の関手とみなし、始対象による Hom 表示の自然性を適用する。
規約：制限前後の余錐は同じ頂点を持つ。使われ方：二枝交換と写像空間の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：余極限を保つ形状の制限は余錐空間の Hom 表示と可換。
方針：coslice 制限の底への可換性と始対象の Hom 比較の自然性を使う。
規約：元の余錐と制限余錐の余極限性を仮定する。使われ方：形状変更の連結成分での計算。 -/
lemma coconeMappingSpacePiZeroEquiv_restrict {K L X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (i : L ⟶ K)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (c.restrict i)) (y : X _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y)) :
    eqToHom (congrArg (fun x => (SSet.HomotopyCategory.mk x : hoFunctor.obj X))
      (c.vertex_restrict i).symm) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv (c.restrict i) hi y
          (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p i y) a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y a := by
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialFiberPiZeroEquiv_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (i ≫ p)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection p i) c hc (c.restrict i) hi rfl y a

/-- 概要：同型な形状による余錐の制限は Hom 表示と可換。
方針：同型による余極限性の保存を一般の自然性に与える。
規約：形状の射の IsIso のみを要求する。使われ方：span の二枝交換。 -/
lemma coconeMappingSpacePiZeroEquiv_reindex {K L X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (i : L ⟶ K) [IsIso i]
    (y : X _⦋0⦌) (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y)) :
    eqToHom (congrArg (fun x => (SSet.HomotopyCategory.mk x : hoFunctor.obj X))
      (c.vertex_restrict i).symm) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv (c.restrict i)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso c i).1 hc) y
            (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p i y) a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y a :=
  coconeMappingSpacePiZeroEquiv_restrict c hc i
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso c i).1 hc) y a

/-- 概要：span の二枝交換による余錐空間の作用は制限した余極限余錐の Hom 表示と可換。
方針：二枝交換の同型を形状変更の自然性へ適用する。
規約：この段階は交換した余錐での表示。使われ方：標準懸垂比較への接続。 -/
lemma coconeMappingSpacePiZeroEquiv_spanSwap {X : SSet.{u}} [Quasicategory X]
    {p : (horn 2 0 : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (y : X _⦋0⦌) (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y)) :
    eqToHom (congrArg (fun x => (SSet.HomotopyCategory.mk x : hoFunctor.obj X))
      (c.vertex_restrict _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap).symm) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv (c.restrict _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso c _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwapIso.hom).1 hc) y
            (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap y) a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y a :=
  coconeMappingSpacePiZeroEquiv_reindex c hc _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwapIso.hom y a

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
