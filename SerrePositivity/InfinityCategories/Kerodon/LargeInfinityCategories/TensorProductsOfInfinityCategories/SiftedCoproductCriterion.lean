module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedInfinity
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Filtered.FilteredBinaryDiagonal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialTerminalWeakContractibility

/-!
概要：非空な ∞ 圏の二項余積の存在から sifted 性を得る。
方針：二点図式の余錐圏の始対象で弱可縮性を示し、全対角の cofinality へ移す。
規約：通常のホモトピー圏の余積ではなく、元の全余錐の余極限を使う。
使われ方：P_Σ の元の圏の sifted 性と、密度余錐による生成。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories

/-- 同じ形状の全図式に余極限が存在すれば、その全定値図式関手は right cofinal。 -/
lemma constantDiagram_isRightCofinal_of_hasColimits (K C : SSet.{u}) [Quasicategory C]
    (h : ∀ p : K ⟶ C, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K C) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_constantDiagram_iff K C).mpr
  intro p
  obtain ⟨c, hc⟩ := h p
  exact hc.isWeaklyContractible

/-- 元の二点図式の余極限が全て存在すれば、元の二項対角は right cofinal。 -/
lemma binaryDiagonal_isRightCofinal_of_hasCoproducts (C : SSet.{u}) [Quasicategory C]
    (h : ∀ p : (Δ[0] : SSet.{u}) ⨿ (Δ[0] : SSet.{u}) ⟶ C, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (lift (𝟙 C) (𝟙 C)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coproductFunctorIso (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}) C
  let d := (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pointFunctorIso C).symm ⊗ᵢ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pointFunctorIso C).symm
  have ht := (constantDiagram_isRightCofinal_of_hasColimits _ C h).comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso e.hom).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso d.hom))
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram ((Δ[0] : SSet.{u}) ⨿ (Δ[0] : SSet.{u})) C ≫
      e.hom ≫ d.hom = lift (𝟙 C) (𝟙 C) := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.constantDiagram_coproductFunctorIso]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [d, tensorIso_hom, lift_fst]
      exact (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pointFunctorIso C).hom_inv_id
    · simp only [d, tensorIso_hom, lift_snd]
      exact (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pointFunctorIso C).hom_inv_id
  rwa [he] at ht

/-- 非空性と元の二項余積の存在だけで、元の ∞ 圏は sifted。 -/
lemma isSiftedInfinity_of_hasBinaryCoproducts (C : SSet.{u}) [Quasicategory C]
    (h₀ : Nonempty (C _⦋0⦌))
    (h₂ : ∀ p : (Δ[0] : SSet.{u}) ⨿ (Δ[0] : SSet.{u}) ⟶ C, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity C :=
  ⟨h₀, binaryDiagonal_isRightCofinal_of_hasCoproducts C h₂⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
