module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CommaSectionFiber
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaUnitComponent
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UniversalUnitComma

/-!
概要：選び直した単位の comma 頂点の元の辺と、その Hom 類を照合する。
方針：二重 fiber の回収公式と、元の単位ホモトピーの持ち上げの往復を使う。
規約：単位の代表の選択を変更しない。使われ方：始対象性の代表不変性への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 指定単位の comma 頂点を、元の F(x) 上の二重 fiber の点として保持。 -/
def unitCommaSectionTargetFiberVertex {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) :
    (vertexFiber (SerrePositivity.InfinityCategories.F1B.unitCommaFiberProjection G x)
      (F.app (Opposite.op ⦋0⦌) x)) _⦋0⦌ :=
  ⟨unitCommaSectionVertex η x, by
    rw [pinchedConstant_zero]
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (unitCommaSection_target η) (Opposite.op ⦋0⦌)) x⟩

/-- 二重 fiber の指定単位から回収する辺は、同じ選んだホモトピーの頂点辺。 -/
lemma unitCommaSectionTargetFiberArrow_eq {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) :
    commaTargetFiberArrow G x (F.app (Opposite.op ⦋0⦌) x)
      (unitCommaSectionTargetFiberVertex η x) =
        simplicialHomotopyVertexEdge (functorHomHomotopy η) x := by
  apply SSet.Edge.ext
  have he := congrArg SSet.Edge.edge
    (commaSectionTargetFiberArrow_eq G (unitCommaSection η) (unitCommaSection_source η) x)
  change (commaTargetFiberArrow G x (F.app (Opposite.op ⦋0⦌) x)
    (unitCommaSectionTargetFiberVertex η x)).edge =
      (unitCommaHomotopy (unitCommaLift G (𝟙 X) F (functorHomHomotopy η))).h.app
        (Opposite.op ⦋1⦌)
        ((Truncated.Edge.id (X := (truncation 2).obj X) x).edge,
          homotopyIntervalEdge.edge) at he
  rw [unitCommaLift_homotopy_h] at he
  exact he

/-- 指定単位の二重 fiber の矢印の類は、元の単位の各点での成分。 -/
lemma unitCommaSectionTargetFiberArrow_hom {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) :
    Truncated.HomotopyCategory.homMk
      (commaTargetFiberArrow G x (F.app (Opposite.op ⦋0⦌) x)
        (unitCommaSectionTargetFiberVertex η x)).toTruncated = qcatUnitComponent η x := by
  rw [unitCommaSectionTargetFiberArrow_eq]
  exact (functorHomEvaluate_homotopy (functorHomHomotopy η) x).symm.trans
    (congrArg (fun α ↦ functorHomEvaluate α x) (functorHomHomotopy_hom η))

end SerrePositivity.InfinityCategories.HomotopyLimits
