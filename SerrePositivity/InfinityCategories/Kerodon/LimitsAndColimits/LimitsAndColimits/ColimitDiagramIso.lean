module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitExistenceTransfer
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceRestrictionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceCylinderFunctorIso
public import Mathlib.Tactic.CrossRefAttribute

/-! # 同型な図式の余極限の存在

概要：関手 quasicategory のホモトピー圏で同型な図式は余極限の存在が同値である。
方針：可逆円柱へ延長し、同値な形状である両端への coslice 制限を使う。
規約：図式の値域のみ quasicategory。使われ方：指定した零枝への cofiber の輸送。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：同値な単射の形状による制限は余極限の存在を保ち反映する。
方針：coslice 制限の trivial Kan fibration 性を余極限の存在の転送に適用する。
規約：形状に quasicategory 性を仮定しない。使われ方：可逆円柱の両端での判定。 -/
lemma hasColimit_iff_restrict_of_precompositionEquivalence {K L X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (f : L ⟶ K) [Mono f]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (f ≫ p) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence p f hf
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_of_trivialRestriction p f

/-- 概要：同値な形状への制限で選んだ余極限余錐は全体へ厳密に延長できる。
方針：trivial な coslice 制限に沿う厳密な延長を適用する。
規約：部分余錐と頂点を等号で保つ。使われ方：可逆円柱上の余極限の選択。 -/
lemma exists_colimitCocone_extension_of_precompositionEquivalence {K L X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (f : L ⟶ K) [Mono f]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ p)) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ∧ c.restrict f = d ∧ c.vertex = d.vertex := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence p f hf
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCocone_extension_of_trivialRestriction p f d hd

/-- 概要：可逆円柱の両端の図式は余極限の存在が同値である。
方針：両端の包含の前合成同値条件を用い、円柱全体の余極限と比較する。
規約：円柱の実際の射を入力する。使われ方：同型な図式の間の輸送。 -/
lemma hasColimit_iff_equivalenceCylinder_endpoints {K X : SSet.{u}} [Quasicategory X]
    (H : K ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint K false ≫ H) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint K true ≫ H) :=
  (hasColimit_iff_restrict_of_precompositionEquivalence H _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_equivalenceCylinderEndpoint K false)).symm.trans
      (hasColimit_iff_restrict_of_precompositionEquivalence H _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_equivalenceCylinderEndpoint K true))

/-- 概要：同型な図式は余極限の存在が同値である。
方針：図式の同型を可逆円柱へ延長し、その両端で余極限の存在を判定する。
規約：関手単体集合のホモトピー圏の同型を使う。
使われ方：零対象や零枝の選択を変更する cofiber の存在の輸送。 -/
@[kerodon 02K2]
lemma hasColimit_iff_of_functorIso {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso p q) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit q := by
  obtain ⟨H, h₀, h₁⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_equivalenceCylinder_extension_of_functorIso e
  have h := hasColimit_iff_equivalenceCylinder_endpoints H
  rw [h₀, h₁] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
