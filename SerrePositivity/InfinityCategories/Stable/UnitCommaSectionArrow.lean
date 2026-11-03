module
public import SerrePositivity.InfinityCategories.Stable.UnitCommaArrowNaturality
public import SerrePositivity.InfinityCategories.Stable.HomotopyVertexArrow
public import SerrePositivity.InfinityCategories.Core.HomotopyInvertibility
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaUnitComponent

/-!
概要：指定 loop 単位と任意の実パラメータ族の comma 矢印の可逆性。
方針：端点輸送を Arrow の等号に保ち、同じ一次単体を照合する。
規約：追加の基準矢印の可逆性を仮定しない。使われ方：元の loop 四角形の普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ実ホモトピーの頂点辺を保つ comma の比較。 -/
lemma unitCommaFiberArrowHom_section_vertexEdge {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) :
    (simplicialHomotopyVertexEdge
      (unitCommaFiberHomotopy (𝟙 (unitCommaFiber G x))) (unitCommaSectionVertex η x)).edge =
      (simplicialHomotopyVertexEdge (functorHomHomotopy η) x).edge := by
  let u := unitCommaSectionVertex η x
  let i : (Δ[0] : SSet.{u}) ⟶ unitCommaFiber G x := SSet.const u
  let H := unitCommaFiberHomotopy (𝟙 (unitCommaFiber G x))
  have hpre : (unitCommaFiberHomotopy i).h = (i ▷ (Δ[1] : SSet.{u})) ≫ H.h := by
    exact (congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ unitCommaFiber G x ↦
      (unitCommaFiberHomotopy f).h) (Category.comp_id i)).symm.trans
        (unitCommaFiberHomotopy_precomp i (𝟙 (unitCommaFiber G x)))
  have hc : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      ((SSet.const x : (Δ[0] : SSet.{u}) ⟶ X) ▷ (Δ[1] : SSet.{u})) ≫
        (functorHomHomotopy η).h :=
    hpre.symm.trans (unitCommaSectionVertex_homotopy_const (A := Δ[0]) η x)
  have he := congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[0] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))).edge, homotopyIntervalEdge.edge)) hc
  change H.h.app (Opposite.op ⦋1⦌) (PinchedHom.constant u 1, homotopyIntervalEdge.edge) =
    (functorHomHomotopy η).h.app (Opposite.op ⦋1⦌)
      (PinchedHom.constant x 1, homotopyIntervalEdge.edge) at he
  rw [pinchedConstant_one, pinchedConstant_one] at he
  exact he

/-- 同じ実ホモトピーの頂点辺を保つ comma の比較。 -/
lemma unitCommaFiberArrowHom_section_isIso {X Y : SSet.{u}} [Quasicategory X]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G)) [IsIso η]
    (x : X _⦋0⦌) : IsIso (unitCommaFiberArrowHom G x (unitCommaSectionVertex η x)) := by
  have hη : IsInvertibleEdge
      (functorEdgeOfSimplicialHomotopy (functorHomHomotopy η)) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomHomotopy η)))
    rw [functorHomHomotopy_hom]
    infer_instance
  have hx := homotopyVertex_isInvertible_of_functorEdge (functorHomHomotopy η) hη x
  have hc : IsInvertibleEdge (simplicialHomotopyVertexEdge
      (unitCommaFiberHomotopy (𝟙 (unitCommaFiber G x)))
        (unitCommaSectionVertex η x)).toTruncated :=
    (isInvertibleEdge_congr (unitCommaFiberArrowHom_section_vertexEdge η x)).mpr hx
  exact homotopyNatTransOfEndpoints_app_isIso_of_vertexEdge _ _ hc
end SerrePositivity.InfinityCategories
