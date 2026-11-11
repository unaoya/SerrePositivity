module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinTransform

/-!
概要：左右に頂点がある場合の fat join の円柱包含の全射性。
方針：左右の包含を円柱を経由する射として表し、既存の射の外延性を使う。
規約：左右の因子の頂点の非空性を明記する。
使われ方：Kerodon §4.6.2（Tag 01HM） の標準単体の比較の合成の検証。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：左右の因子に頂点が存在すれば fat join の円柱包含はエピ射。
方針：他方の頂点を定数として両因子の包含を円柱へ持ち上げる。
規約：因子の quasicategory 性は不要。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の標準単体の円柱上での検証。 -/
instance fatJoinCylinder_epi_of_nonempty (A B : SSet.{u})
    [Nonempty (A _⦋0⦌)] [Nonempty (B _⦋0⦌)] : Epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B) where
  left_cancellation f g h := by
    obtain ⟨a⟩ := (inferInstance : Nonempty (A _⦋0⦌))
    obtain ⟨b⟩ := (inferInstance : Nonempty (B _⦋0⦌))
    let l : A ⟶ (A ⊗ (Δ[1] : SSet.{u})) ⊗ B := lift SSet.ι₀ (SSet.const b)
    let r : B ⟶ (A ⊗ (Δ[1] : SSet.{u})) ⊗ B := lift (SSet.const a ≫ SSet.ι₁) (𝟙 B)
    have hl : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B := by
      simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_lift_zero (𝟙 A) (SSet.const b)
    have hr : r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B := by
      simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_lift_one (SSet.const a) (𝟙 B)
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin_hom_ext h
    · have he := congrArg (fun k ↦ l ≫ k) h
      simpa only [← Category.assoc, hl] using he
    · have he := congrArg (fun k ↦ r ≫ k) h
      simpa only [← Category.assoc, hr] using he

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
