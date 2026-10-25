module

public import SerrePositivity.InfinityCategories.F2.Ind.EmptyShapeTensor
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramRightPrismRecovery

/-!
概要：元の空形状の diagram comma では、任意の全試験族が一意に存在する。
方針：C 全族と全円柱を始対象から作り、同じ二全成分で一意性を検査する。
規約：C に対象の非空性を課さず、元の全図式 D を保持する。
使われ方：空の有限半順序図式の実余錐と単一 filtered 表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C) (hK : ¬ K.Nonempty)
/-- 概要：元の空形状の comma への任意の試験族の全写像を構成する。
方針：元の二全成分を始対象から作る。規約：元の D。使われ方：空形状の基底。 -/
def emptyDiagramCommaFamily (T : SSet.{u + 1}) : T ⟶ diagramComma κ D :=
  diagramRightPrismFamily κ D
    ((emptyShapeTensorIsInitial hK T).to _)
    ((emptyShapeTensorIsInitial hK (join T (Δ[0] : SSet.{u + 1}))).to _)
    ((emptyShapeTensorIsInitial hK T).hom_ext _ _)
    ((emptyShapeTensorIsInitial hK (Δ[0] : SSet.{u + 1})).hom_ext _ _)
include hK
/-- 概要：元の空形状の同じ comma への任意の全族は等しい。
方針：元の C 全族と全円柱の一意性。規約：全射の等号。使われ方：旧族の厳密回収。 -/
lemma emptyDiagramComma_hom_ext {T : SSet.{u + 1}} (q r : T ⟶ diagramComma κ D) : q = r := by
  apply diagramComma_rightFamily_ext κ D
  · exact (emptyShapeTensorIsInitial hK T).hom_ext _ _
  · exact (emptyShapeTensorIsInitial hK (join T (Δ[0] : SSet.{u + 1}))).hom_ext _ _
/-- 概要：元の空形状の同じ comma の任意の全試験族には実余錐がある。
方針：全余錐写像を作り一意性で旧族を回収。規約：元の q。使われ方：帰納の基底。 -/
lemma nonempty_emptyDiagramComma_cocone {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D) :
    Nonempty (JoinCocone q) :=
  ⟨⟨emptyDiagramCommaFamily κ D hK (join T (Δ[0] : SSet.{u + 1})),
    emptyDiagramComma_hom_ext κ D hK _ _⟩⟩
end SerrePositivity.InfinityCategories.F2.Ind
