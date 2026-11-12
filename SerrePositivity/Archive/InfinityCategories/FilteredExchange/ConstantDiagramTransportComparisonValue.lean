module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantDiagramTransportComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalComparisonComposition

/-!
概要：元の定値図式の指定輸送比較を、同じ区間の任意の指定持ち上げを経由して表示する。
方針：元の比較の終点表示の補正を除き、元の普遍比較の厳密な合成則を使う。
規約：元の比較を選び直さない。使われ方：下側因子を元の全三角形の持ち上げへ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {T : SSet.{u + 1}} (B : SSet.{u + 1}) {x y : SpaceInfinity.{u} _⦋0⦌}
  (a : T ⟶ intervalMappingSpace x y)
local notation "P" => constantUnstraighteningFiberProjection B x
local notation "w₀" => constantDiagramTransportWitness (constantDiagramMappingFamilyWitness B a)

/-- 元の定値図式の指定比較は、元の pointed 証拠の普遍輸送への指定比較と同じ値。 -/
lemma constantDiagramMappingTransportIso_heq_witness :
    HEq (constantDiagramMappingTransportIso B a)
      (pointedIntervalTransportComparison P a w₀) := by
  unfold constantDiagramMappingTransportIso
  have hcast {α β : Sort (u + 2)} (h : α = β) (e : α) : HEq (Eq.mp h e) e := by
    cases h
    rfl
  exact hcast _ _

/-- 元の定値図式の指定比較は、同じ区間の指定持ち上げを経由しても値を保つ。 -/
lemma constantDiagramMappingTransportIso_heq_via
    (w : FiberTransportFamily (b := y) pointedSpaceProjection P (intervalMappingUncurry a)) :
    HEq (constantDiagramMappingTransportIso B a)
      ((w₀).endpointIso pointedSpaceProjection P (intervalMappingUncurry a)
        (intervalMappingUncurry_one a) w ≪≫ pointedIntervalTransportComparison P a w) :=
  (constantDiagramMappingTransportIso_heq_witness B a).trans
    (heq_of_eq (pointedIntervalTransportComparison_trans P a w₀ w)).symm

end SerrePositivity.InfinityCategories.F2
