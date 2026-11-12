module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UnitCommaSectionArrow
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberExtension

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ実ホモトピーの頂点辺を保つ comma の比較。 -/
lemma unitCommaFiberArrowHom_family_vertexEdge {A X Y : SSet.{u}}
    {G : Y ⟶ X} {x : X _⦋0⦌} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) (a : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)))
      (f.app (Opposite.op ⦋0⦌) a)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy f) a).edge := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x))
  have hpre : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy f).h = (f ▷ (Δ[1] : SSet.{u})) ≫ H.h :=
    (congrArg (fun q : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy q).h)
      (Category.comp_id f)).symm.trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy_precomp f (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x)))
  have hid : f.app (Opposite.op ⦋1⦌)
      (SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x))
        (f.app (Opposite.op ⦋0⦌) a)).edge :=
    ConcreteCategory.congr_hom (f.naturality (SimplexCategory.σ (0 : Fin 1)).op) a
  have he := congrArg (fun q ↦ q.app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) hpre
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy f).h.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
    H.h.app (Opposite.op ⦋1⦌)
      (f.app (Opposite.op ⦋1⦌) (SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) at he
  rw [hid] at he
  exact he.symm

/-- 同じ実ホモトピーの頂点辺を保つ comma の比較。 -/
lemma unitCommaFiberArrowHom_isIso_of_family_vertexEdge {A X Y : SSet.{u}}
    {G : Y ⟶ X} {x : X _⦋0⦌} (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) (a : A _⦋0⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy f) a).toTruncated) :
    IsIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiberArrowHom G x (f.app (Opposite.op ⦋0⦌) a)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homotopyNatTransOfEndpoints_app_isIso_of_vertexEdge _ _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (unitCommaFiberArrowHom_family_vertexEdge f a)).mpr he)

/-- 同じ実ホモトピーの頂点辺を保つ comma の比較。 -/
lemma unitCommaFiberArrowHom_curry_isIso {A X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌)
    (b : A ⟶ Y) (H : SSet.Homotopy (SSet.const x) (b ≫ G)) (a : A _⦋0⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).toTruncated) :
    IsIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.unitCommaFiberArrowHom G x
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry G x b H).app (Opposite.op ⦋0⦌) a)) := by
  apply unitCommaFiberArrowHom_isIso_of_family_vertexEdge
  have heq : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry G x b H)) a).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).edge :=
    congrArg (fun q ↦ q.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_homotopy G x b H)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr heq).mpr he
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
