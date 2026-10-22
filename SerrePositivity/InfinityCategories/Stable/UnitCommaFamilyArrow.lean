module
public import SerrePositivity.InfinityCategories.Stable.UnitCommaSectionArrow
public import SerrePositivity.InfinityCategories.F1B.UnitCommaFiberExtension

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
lemma unitCommaFiberArrowHom_family_vertexEdge {A X Y : SSet.{u}}
    {G : Y ⟶ X} {x : X _⦋0⦌} (f : A ⟶ unitCommaFiber G x) (a : A _⦋0⦌) :
    (simplicialHomotopyVertexEdge (unitCommaFiberHomotopy (𝟙 (unitCommaFiber G x)))
      (f.app (Opposite.op ⦋0⦌) a)).edge =
      (simplicialHomotopyVertexEdge (unitCommaFiberHomotopy f) a).edge := by
  let H := unitCommaFiberHomotopy (𝟙 (unitCommaFiber G x))
  have hpre : (unitCommaFiberHomotopy f).h = (f ▷ (Δ[1] : SSet.{u})) ≫ H.h :=
    (congrArg (fun q : A ⟶ unitCommaFiber G x ↦ (unitCommaFiberHomotopy q).h)
      (Category.comp_id f)).symm.trans
        (unitCommaFiberHomotopy_precomp f (𝟙 (unitCommaFiber G x)))
  have hid : f.app (Opposite.op ⦋1⦌)
      (SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj (unitCommaFiber G x))
        (f.app (Opposite.op ⦋0⦌) a)).edge :=
    ConcreteCategory.congr_hom (f.naturality (SimplexCategory.σ (0 : Fin 1)).op) a
  have he := congrArg (fun q ↦ q.app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge,
      homotopyIntervalEdge.edge)) hpre
  change (unitCommaFiberHomotopy f).h.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge,
        homotopyIntervalEdge.edge) =
    H.h.app (Opposite.op ⦋1⦌)
      (f.app (Opposite.op ⦋1⦌) (SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge,
        homotopyIntervalEdge.edge) at he
  rw [hid] at he
  exact he.symm

/-- 同じ実ホモトピーの頂点辺を保つ comma の比較。 -/
lemma unitCommaFiberArrowHom_isIso_of_family_vertexEdge {A X Y : SSet.{u}}
    {G : Y ⟶ X} {x : X _⦋0⦌} (f : A ⟶ unitCommaFiber G x) (a : A _⦋0⦌)
    (he : IsInvertibleEdge
      (simplicialHomotopyVertexEdge (unitCommaFiberHomotopy f) a).toTruncated) :
    IsIso (unitCommaFiberArrowHom G x (f.app (Opposite.op ⦋0⦌) a)) :=
  homotopyNatTransOfEndpoints_app_isIso_of_vertexEdge _ _
    ((isInvertibleEdge_congr (unitCommaFiberArrowHom_family_vertexEdge f a)).mpr he)

/-- 同じ実ホモトピーの頂点辺を保つ comma の比較。 -/
lemma unitCommaFiberArrowHom_curry_isIso {A X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌)
    (b : A ⟶ Y) (H : SSet.Homotopy (SSet.const x) (b ≫ G)) (a : A _⦋0⦌)
    (he : IsInvertibleEdge (simplicialHomotopyVertexEdge H a).toTruncated) :
    IsIso (unitCommaFiberArrowHom G x
      ((unitCommaFiberCurry G x b H).app (Opposite.op ⦋0⦌) a)) := by
  apply unitCommaFiberArrowHom_isIso_of_family_vertexEdge
  have heq : (simplicialHomotopyVertexEdge
      (unitCommaFiberHomotopy (unitCommaFiberCurry G x b H)) a).edge =
      (simplicialHomotopyVertexEdge H a).edge :=
    congrArg (fun q ↦ q.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge,
        homotopyIntervalEdge.edge)) (unitCommaFiberCurry_homotopy G x b H)
  exact (isInvertibleEdge_congr heq).mpr he
end SerrePositivity.InfinityCategories
