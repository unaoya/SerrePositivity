module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinRealization
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinPrismOpposite

/-!
概要：反転した左写像円柱による右指定変換の円柱表示。
方針：δ の反転の左円柱を反転し、二重反転の同型で元の係数へ戻す。
規約：右円柱はこの反転模型を定義として用い、元の α の回収を射の等式で検査する。
使われ方：任意の δ に対する右相対 join 表示の比較の始域。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：右写像円柱を反転した左円柱として定義する。
方針：Kop の終点を δop で貼った pushout を反転する。
規約：通常の pushout (ι₀) δ との同型をこの定義の前提にしない。
使われ方：右指定変換の一つの円柱全体の比較。 -/
abbrev KanRightCylinder {K C : SSet.{u}} (δ : K ⟶ C) : SSet.{u} :=
  (pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K.op) (SSet.opFunctor.map δ)).op

/-- 概要：右円柱の prism 部分の包含。
方針：時間を第一因子へ移し、二重反転した K と反転した区間付き係数へ写す。
規約：始域は K×Δ¹。
使われ方：右円柱図式が元の α を保持することの検査。 -/
def kanRightCylinderPrism {K C : SSet.{u}} (δ : K ⟶ C) :
    K ⊗ (Δ[1] : SSet.{u}) ⟶ KanRightCylinder δ :=
  (β_ K (Δ[1] : SSet.{u})).hom ≫
    ((Δ[1] : SSet.{u}) ◁ (SSet.opFunctorCompOpFunctorIso.app K).inv) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPrismOppositeIso K.op).inv ≫
    SSet.opFunctor.map (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K.op) (SSet.opFunctor.map δ))

/-- 概要：右円柱の底 C の包含。
方針：C の二重反転へ写し、左円柱の C.op 側の包含を反転する。
規約：元の C を始域に持つ。
使われ方：右円柱図式の底図式 F の回収。 -/
def kanRightCylinderBase {K C : SSet.{u}} (δ : K ⟶ C) : C ⟶ KanRightCylinder δ :=
  (SSet.opFunctorCompOpFunctorIso.app C).inv ≫
    SSet.opFunctor.map (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K.op) (SSet.opFunctor.map δ))

/-- 概要：右円柱の prism の始点は δ に沿う底の包含に等しい。
方針：反転した左円柱の終点の貼り合わせと二重反転同型の自然性を使う。
規約：時間は第二因子。
使われ方：一つの円柱比較の始端を両端図式の左成分へ移す。 -/
lemma kanRightCylinderPrism_zero {K C : SSet.{u}} (δ : K ⟶ C) :
    SSet.ι₀ ≫ kanRightCylinderPrism δ = δ ≫ kanRightCylinderBase δ := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫
    ((Δ[1] : SSet.{u}) ◁ (SSet.opFunctorCompOpFunctorIso.app K).inv) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K.op) (SSet.opFunctor.map δ)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc]
  change (SSet.opFunctorCompOpFunctorIso.app K).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K.op.op ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K.op) (SSet.opFunctor.map δ))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_endpoint]
  change (SSet.opFunctorCompOpFunctorIso.app K).inv ≫
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K.op ≫ pushout.inl _ _) = _
  rw [pushout.condition, CategoryTheory.Functor.map_comp]
  have hn : (SSet.opFunctorCompOpFunctorIso.app K).inv ≫
      SSet.opFunctor.map (SSet.opFunctor.map δ) =
      δ ≫ (SSet.opFunctorCompOpFunctorIso.app C).inv :=
    SSet.opFunctorCompOpFunctorIso.inv.naturality δ
  rw [← Category.assoc, hn]
  rfl

/-- 概要：右指定変換を反転した左指定変換を、合成の表示も含めて型付けする。
方針：反転ホモトピーの raw な射を保ち、終端で関手の合成保存を使う。
規約：終端を δop≫Fop と明示する。
使われ方：左円柱図式へ反転した α を型の移送なしに渡す。 -/
def rightKanOppositeTransformation {K C D : SSet.{u}} (δ : K ⟶ C)
    (F₀ : K ⟶ D) (F : C ⟶ D) (α : SSet.Homotopy (δ ≫ F) F₀) :
    SSet.Homotopy (SSet.opFunctor.map F₀)
      (SSet.opFunctor.map δ ≫ SSet.opFunctor.map F) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite α).h
  h₀ := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite α).h₀
  h₁ := by
    change SSet.ι₁ ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite α).h =
      SSet.opFunctor.map δ ≫ SSet.opFunctor.map F
    simpa only [CategoryTheory.Functor.map_comp] using (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite α).h₁
  rel := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homotopyOpposite α).rel

/-- 概要：元の右指定変換を持つ右円柱図式。
方針：反転した α の左円柱図式を反転し、標的の二重反転を消去する。
規約：α の入力の向きは δ≫F から F₀。
使われ方：相対 join 上の表示が比較する一つの図式。 -/
def rightKanCylinderDiagram {K C D : SSet.{u}} (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D)
    (α : SSet.Homotopy (δ ≫ F) F₀) : KanRightCylinder δ ⟶ D :=
  SSet.opFunctor.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCylinderDiagram (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀)
      (SSet.opFunctor.map F) (rightKanOppositeTransformation δ F₀ F α)) ≫
    (SSet.opFunctorCompOpFunctorIso.app D).hom

/-- 概要：右円柱図式の prism 部分は元の α の射に厳密に等しい。
方針：pushout の制限を計算し、prism の二重反転を消去する。
規約：端点だけでなく全時間で指定変換を回収する。
使われ方：反転模型が任意の元の右指定変換を保持することの根拠。 -/
lemma kanRightCylinderPrism_diagram {K C D : SSet.{u}} (δ : K ⟶ C)
    (F₀ : K ⟶ D) (F : C ⟶ D) (α : SSet.Homotopy (δ ≫ F) F₀) :
    kanRightCylinderPrism δ ≫ rightKanCylinderDiagram δ F₀ F α = α.h := by
  simp only [kanRightCylinderPrism, rightKanCylinderDiagram, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCylinderDiagram]
  rw [← Category.assoc (SSet.opFunctor.map (pushout.inl _ _)),
    ← CategoryTheory.Functor.map_comp, pushout.inl_desc]
  change (β_ K (Δ[1] : SSet.{u})).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.unreversePrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism ((β_ (Δ[1] : SSet.{u}) K).hom ≫ α.h)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.unreversePrism_reversePrism]
  rfl

/-- 概要：右円柱図式の底への制限は元の F に厳密に等しい。
方針：pushout の底への制限と二重反転同型の自然性を使う。
規約：底図式は自然同型でなく射の等式で回収する。
使われ方：右相対 join 表示の底側の比較。 -/
lemma kanRightCylinderBase_diagram {K C D : SSet.{u}} (δ : K ⟶ C)
    (F₀ : K ⟶ D) (F : C ⟶ D) (α : SSet.Homotopy (δ ≫ F) F₀) :
    kanRightCylinderBase δ ≫ rightKanCylinderDiagram δ F₀ F α = F := by
  simp only [kanRightCylinderBase, rightKanCylinderDiagram, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCylinderDiagram]
  rw [← Category.assoc (SSet.opFunctor.map (pushout.inr _ _)),
    ← CategoryTheory.Functor.map_comp, pushout.inr_desc]
  have h : SSet.opFunctor.map (SSet.opFunctor.map F) ≫
      (SSet.opFunctorCompOpFunctorIso.app D).hom =
      (SSet.opFunctorCompOpFunctorIso.app C).hom ≫ F :=
    SSet.opFunctorCompOpFunctorIso.hom.naturality F
  rw [h, Iso.inv_hom_id_assoc]

/-- 概要：右 relative join を左 relative join の反転から回収する同型。
方針：右 relative join の反転同型をもう一度反転し、二重反転を消す。
規約：順方向は反転した左 relative join から右 relative join。
使われ方：左円柱比較を反転した射の標的の同定。 -/
def kanRelativeJoinRightDualIso {K C : SSet.{u}} (δ : K ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (SSet.opFunctor.map δ) (𝟙 C.op)).op ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ :=
  (SSet.opFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinOppositeIso (𝟙 C) δ)).symm ≪≫
    SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ)

/-- 概要：右円柱から右 relative join への比較射。
方針：δop の左円柱比較を反転し、右 relative join の同型で写す。
規約：δ は任意。前合成同値の主張は別に証明する。
使われ方：右相対 join 表示の円柱全体との比較。 -/
def kanRightRelativeJoinCylinderComparison {K C : SSet.{u}} (δ : K ⟶ C) :
    KanRightCylinder δ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ :=
  SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison (SSet.opFunctor.map δ)) ≫
    (kanRelativeJoinRightDualIso δ).hom

/-- 概要：右円柱比較の prism 部分は標準右 prism と厳密に一致する。
方針：左比較の prism 部分を反転し、右 prism の反転を再び戻す。
規約：δ の単射性は不要。
使われ方：右相対 join 表示の円柱比較を元の指定変換へ制限する。 -/
lemma kanRightCylinderPrism_comparison {K C : SSet.{u}} (δ : K ⟶ C) :
    kanRightCylinderPrism δ ≫ kanRightRelativeJoinCylinderComparison δ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism δ := by
  let E : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ).op ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (SSet.opFunctor.map δ) (𝟙 C.op) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinOppositeIso (𝟙 C) δ
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism (SSet.opFunctor.map δ) ≫ E.inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism ((β_ (Δ[1] : SSet.{u}) K).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism δ) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism_reverse δ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [kanRightCylinderPrism, kanRightRelativeJoinCylinderComparison, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inl]
  change (β_ K (Δ[1] : SSet.{u})).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.unreversePrism (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism (SSet.opFunctor.map δ) ≫ E.inv) = _
  rw [hp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.unreversePrism_reversePrism]
  rfl

/-- 概要：右円柱比較は底 C の包含を右 relative join の左包含へ移す。
方針：左比較の底の式、反転による包含の交換、二重反転の自然性を使う。
規約：C 全体での射の等式。
使われ方：右相対 join 表示の底側の同型。 -/
lemma kanRightCylinderBase_comparison {K C : SSet.{u}} (δ : K ⟶ C) :
    kanRightCylinderBase δ ≫ kanRightRelativeJoinCylinderComparison δ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ := by
  let E : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ).op ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (SSet.opFunctor.map δ) (𝟙 C.op) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinOppositeIso (𝟙 C) δ
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (SSet.opFunctor.map δ) (𝟙 C.op) ≫ E.inv =
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ) := by
    have hx : SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ) ≫ E.hom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (SSet.opFunctor.map δ) (𝟙 C.op) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinOppositeIso_inl (𝟙 C) δ
    rw [← hx, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [kanRightCylinderBase, kanRightRelativeJoinCylinderComparison, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inr]
  change (SSet.opFunctorCompOpFunctorIso.app C).inv ≫
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (SSet.opFunctor.map δ) (𝟙 C.op)) ≫
    SSet.opFunctor.map E.inv ≫
    (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ)).hom = _
  rw [← CategoryTheory.Functor.map_comp_assoc, hi]
  have hn : SSet.opFunctor.map (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ)) ≫
      (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ)).hom =
      (SSet.opFunctorCompOpFunctorIso.app C).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ :=
    SSet.opFunctorCompOpFunctorIso.hom.naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ)
  rw [hn, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
