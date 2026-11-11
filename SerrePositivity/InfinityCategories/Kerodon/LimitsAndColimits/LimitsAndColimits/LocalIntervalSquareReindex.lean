module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LocalIntervalDiagramEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.HomFixedComponentPrism

/-!
概要：標準正方形を元の底の prism に戻し、同じ三辺の固定条件を保持する。
方針：底の同型の逆を前合成し、端点の自然性と指定頂点の保持で計算する。
規約：標準正方形と元の prism の往復は厳密な等式。
使われ方：外ホーン延長の二三角形から、実際の固定成分 Hom の族を構成する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

local notation "B" => (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHomDiagramBase (ULift (Fin 2)))

/-- 同じ指定頂点の側辺は、底の逆同型を通しても元の側辺を回収する。 -/
lemma localIntervalDiagramBaseIso_side_inv (i : Fin 2) :
    lift (𝟙 (Δ[1] : SSet.{u + 1}))
        (SSet.const (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up i : ULift.{u} (Fin 2))))) ≫
      (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} 1).inv) =
    lift (𝟙 (Δ[1] : SSet.{u + 1})) (SSet.const (stdSimplex.obj₀Equiv.symm i)) := by
  have h := congrArg (fun r => r ≫ (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} 1).inv))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.localIntervalDiagramBaseIso_side.{u} i)
  have hf : (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} 1).hom) ≫
      (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} 1).inv) = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id]
  simpa only [Category.assoc, hf, Category.comp_id] using h.symm

/-- 元の標準正方形を、同じ底の元の prism へ戻す。 -/
def localIntervalSquareReindex {T X : SSet.{u + 1}}
    (H : ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ T ⟶ X) : (Δ[1] ⊗ B) ⊗ T ⟶ X :=
  ((Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} 1).inv) ▷ T) ≫ H

/-- 標準正方形を元の底へ戻して再び標準化すると、元の正方形そのもの。 -/
lemma localIntervalSquareReindex_forward {T X : SSet.{u + 1}}
    (H : ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ T ⟶ X) :
    ((Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso.{u} 1).hom) ▷ T) ≫ localIntervalSquareReindex H = H := by
  unfold localIntervalSquareReindex
  rw [← Category.assoc, ← comp_whiskerRight, ← MonoidalCategory.whiskerLeft_comp,
    Iso.hom_inv_id, whiskerLeft_id, id_whiskerRight, Category.id_comp]

/-- 標準正方形の同じ端点の固定条件は、元の底の同じ図式の固定条件に戻る。 -/
lemma localIntervalSquareReindex_endpoint {T X : SSet.{u + 1}}
    (H : ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ T ⟶ X) (i : Fin 2) (D : B ⟶ X)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i Δ[1] ▷ T) ≫ H =
      fst (Δ[1] : SSet.{u + 1}) T ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso 1).hom ≫ D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i B ▷ T) ≫ localIntervalSquareReindex H = fst B T ≫ D := by
  unfold localIntervalSquareReindex
  rw [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, comp_whiskerRight,
    Category.assoc, h, ← Category.assoc, whiskerRight_fst, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- 標準正方形の同じ指定頂点の側辺は、元の底の指定頂点の側辺と一致する。 -/
lemma localIntervalSquareReindex_at {T X : SSet.{u + 1}}
    (H : ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ T ⟶ X) (i : Fin 2) :
    (lift (𝟙 (Δ[1] : SSet.{u + 1}))
        (SSet.const (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up i : ULift.{u} (Fin 2))))) ▷ T) ≫
      localIntervalSquareReindex H =
    (lift (𝟙 (Δ[1] : SSet.{u + 1})) (SSet.const (stdSimplex.obj₀Equiv.symm i)) ▷ T) ≫ H := by
  unfold localIntervalSquareReindex
  rw [← Category.assoc, ← comp_whiskerRight, localIntervalDiagramBaseIso_side_inv]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
