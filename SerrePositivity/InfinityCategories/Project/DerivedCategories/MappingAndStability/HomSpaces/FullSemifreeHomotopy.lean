module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.FullSemifreeSubcategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.HomotopyCategoryComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryMap

/-! # 対象条件による全部分圏のホモトピー比較

概要：全部分圏のホモトピー圏を h D(S) の充満部分圏として比較する。
方針：正本と dg nerve モデルの単体的同型、N3 の H⁰ 比較、充満 dg 包含を組み合わせる。
規約：ホモトピー圏は二次切断の辺の類の圏。使われ方：K 理論の入力の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (S : Type u) [CommRing S] (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S → Prop)

/-- 概要：正本の全部分圏のホモトピー圏。
方針：二次切断の辺のホモトピー類を取る。
規約：D3 と同じ規約。使われ方：充満部分圏の比較の始域。 -/
abbrev semifreeFullHomotopyCategory :=
  SSet.Truncated.HomotopyCategory₂
    ((SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullSubcomplex S P : SSet.{u + 1}))

/-- 概要：正本と計算モデルのホモトピー圏は同値である。
方針：単体的同型の両方向が誘導する関手を取る。
規約：順方向は正本から計算モデルへ。使われ方：dg H⁰ との比較。 -/
def semifreeFullModelHomotopyEquivalence : semifreeFullHomotopyCategory S P ≌
    SSet.Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerve S P)) :=
  CategoryTheory.Equivalence.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveIso S P).inv)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullNerveIso S P).hom)
    (eqToIso (by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map_comp, Iso.inv_hom_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map_id]))
    (eqToIso (by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map_comp, Iso.hom_inv_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map_id]))

/-- 概要：全部分圏のホモトピー圏は条件 P を満たす semifree dg 圏の H⁰ と同値である。
方針：計算モデルとの同値を N3 の比較に合成する。
規約：射は閉零射のホモトピー類。使われ方：充満 dg 包含による比較。 -/
def semifreeFullH0Equivalence : semifreeFullHomotopyCategory S P ≌
    DifferentialGraded.HomotopyCategory S (DGFullSubcategory (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) P) :=
  (semifreeFullModelHomotopyEquivalence S P).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equivalence S (DGFullSubcategory (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) P))

/-- 概要：全部分圏の H⁰ から semifree の H⁰ への充満包含。
方針：充満 dg 包含のホモトピー関手を取る。
規約：Hom 複体を保持する。使われ方：h D(S) の充満部分圏。 -/
abbrev semifreeFullH0Inclusion :=
  (dgFullSubcategoryInclusion S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) P).onHomotopy

/-- 概要：h 全部分圏(S) から h D(S) への包含比較。
方針：N3 を通して充満 dg 包含を適用する。
規約：選ばれた同値の逆関手を介して表す。使われ方：対象条件による Hom の同定。 -/
def semifreeFullHomotopyInclusion : semifreeFullHomotopyCategory S P ⥤
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory S :=
  (semifreeFullH0Equivalence S P).functor ⋙ semifreeFullH0Inclusion S P ⋙
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).inverse

/-- 概要：h 全部分圏の包含比較は充満である。
方針：N3 の同値と充満 dg 包含の充満性を合成する。
規約：全ての対象間の射を含む。使われ方：充満部分圏としての同定。 -/
instance semifreeFullHomotopyInclusion_full : (semifreeFullHomotopyInclusion S P).Full := by
  dsimp [semifreeFullHomotopyInclusion, semifreeFullH0Inclusion]
  infer_instance

/-- 概要：h 全部分圏の包含比較は忠実である。
方針：N3 の同値と充満 dg 包含の忠実性を合成する。
規約：周囲と同じホモトピー関係。使われ方：Hom 全単射。 -/
instance semifreeFullHomotopyInclusion_faithful : (semifreeFullHomotopyInclusion S P).Faithful := by
  dsimp [semifreeFullHomotopyInclusion, semifreeFullH0Inclusion]
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories
