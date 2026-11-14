module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.Semifree
public import SerrePositivity.DifferentialGraded.Category.Tensor


/-! # Semifree 複体の充満 dg 部分圏とその H⁰ -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S]

/-- 概要：semifree 複体の充満 dg 部分圏。
方針：対象を semifree 複体に制限し Hom 複体は全複体圏から継承する。
規約：semifree 性は filtration の存在という命題。使われ方：導来圏の dg 表示。 -/
abbrev Semifree := DGFullSubcategory (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S)

/-- 概要：semifree 複体の H⁰ から通常の複体ホモトピー圏への関手。
方針：充満 dg 包含の H⁰ と既存の複体ホモトピー比較を合成する。
規約：比較先は Mathlib の整数余鎖複体の商。使われ方：導来比較の第一段。 -/
def semifreeHomotopyComparison :
    DifferentialGraded.HomotopyCategory S (Semifree S) ⥤
      _root_.HomotopyCategory (ModuleCat.{u} S) (.up ℤ) :=
  (dgFullSubcategoryInclusion S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S)).onHomotopy ⋙
    (complexHomotopyEquivalence S).functor

/-- 概要：H⁰ の比較は充満である。
方針：dg 包含と複体比較の充満性を合成する。規約：係数環は可換。
使われ方：導来比較での射の持ち上げ。 -/
instance semifreeHomotopyComparisonFull : (semifreeHomotopyComparison S).Full := by
  unfold semifreeHomotopyComparison
  infer_instance

/-- 概要：H⁰ の比較は忠実である。
方針：dg 包含と複体比較の忠実性を合成する。規約：境界関係も包含が反映する。
使われ方：導来比較での射の等式の反映。 -/
instance semifreeHomotopyComparisonFaithful : (semifreeHomotopyComparison S).Faithful := by
  unfold semifreeHomotopyComparison
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories
