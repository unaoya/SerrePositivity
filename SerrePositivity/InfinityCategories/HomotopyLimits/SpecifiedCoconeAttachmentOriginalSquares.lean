module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeAttachmentOriginalCoherence
public import SerrePositivity.InfinityCategories.HomotopyLimits.FunctorHomSquareRealization

/-!
概要：元の HL・HR と枝比較・根辺比較・付加辺面比較を四辺に持つ実際の正方形。
方針：同じ型付き端点での合成の等式を、同じ四つの円柱を保って実現する。
規約：四辺の代表を固定。使われ方：共通 path end 内の実際の全族の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (hB : IsColimitCone dB)
  (dC : JoinCocone (j ≫ p)) (hC : IsColimitCone dC) (y : SpaceInfinity.{u} _⦋0⦌)

section
local notation "L" => specifiedCoconeLeftEndHomotopy hp p c hc dB hB dC y
local notation "B₁" => specifiedCoconeLeftBranchLegHomotopy hp p c hc dB hB dC y
local notation "C₁" => specifiedCoconeLeftHomCylinderComparison hp p c hc dB dC y
local notation "D₁" => specifiedCoconeLeftAttachmentHomotopy hp p c hc dB dC y
local notation "cls(" H ")" => SSet.Truncated.HomotopyCategory.homMk
  (functorEdgeOfSimplicialHomotopy H)

/-- 元の左の四円柱の合成則は、同じ型付き端点の射として成立する。 -/
lemma specifiedCoconeLeftAttachment_original_homMk_comp : cls(L) ≫ cls(B₁) = cls(C₁) ≫ cls(D₁) := by
  have h := specifiedCoconeLeftAttachment_original_homMk_comp_arrow hp p c hc dB hB dC y
  obtain ⟨_, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- 元の左 HL・HR を下辺、枝比較を右辺、根辺比較を左辺、付加辺面比較を上辺に保つ。 -/
def specifiedCoconeLeftAttachmentOriginalSquare : SerrePositivity.InfinityCategories.FunctorHomSquare L D₁ C₁ B₁ :=
  (nonempty_functorHomSquare_of_homEq L D₁ C₁ B₁
    (specifiedCoconeLeftAttachment_original_homMk_comp hp p c hc dB hB dC y)).some
end

section
local notation "L" => specifiedCoconeRightEndHomotopy hp p c hc dB dC hC y
local notation "B₁" => specifiedCoconeRightBranchLegHomotopy hp p c hc dB dC hC y
local notation "C₁" => specifiedCoconeRootedHomCylinderComparison hp p c hc dB dC y
local notation "D₁" => specifiedCoconeRightAttachmentHomotopy hp p c hc dB dC y
local notation "cls(" H ")" => SSet.Truncated.HomotopyCategory.homMk
  (functorEdgeOfSimplicialHomotopy H)

/-- 元の右の四円柱の合成則は、同じ型付き端点の射として成立する。 -/
lemma specifiedCoconeRightAttachment_original_homMk_comp :
    cls(L) ≫ cls(B₁) = cls(C₁) ≫ cls(D₁) := by
  have h := specifiedCoconeRightAttachment_original_homMk_comp_arrow hp p c hc dB dC hC y
  obtain ⟨_, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- 元の右 HL・HR を下辺、枝比較を右辺、根辺比較を左辺、付加辺面比較を上辺に保つ。 -/
def specifiedCoconeRightAttachmentOriginalSquare : SerrePositivity.InfinityCategories.FunctorHomSquare L D₁ C₁ B₁ :=
  (nonempty_functorHomSquare_of_homEq L D₁ C₁ B₁
    (specifiedCoconeRightAttachment_original_homMk_comp hp p c hc dB dC hC y)).some
end

end
end SerrePositivity.InfinityCategories.HomotopyLimits
