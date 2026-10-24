module
public import SerrePositivity.InfinityCategories.Stable.UnitCommaArrowNaturality
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Stable.InitialTransport

/-!
概要：固定始域 comma の実矢印と始対象性、指定 loop 単位の可逆性。
方針：実ホモトピーの Ho 自然性と left fibration の可逆性反映を使う。
規約：生の関手値の端点を保つ。使われ方：元の loop 四角形の押し出し性の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ comma の実矢印と始対象性の比較。 -/
lemma unitCommaFiber_isInitial_of_invertibleArrow {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X) (hG : IsFullyFaithful G)
    (x : X _⦋0⦌) (u : (unitCommaFiber G x) _⦋0⦌) (hu : IsInitialVertex u)
    (huA : IsIso (unitCommaFiberArrowHom G x u))
    (v : (unitCommaFiber G x) _⦋0⦌) (hvA : IsIso (unitCommaFiberArrowHom G x v)) :
    IsInitialVertex v := by
  obtain ⟨e⟩ := hu.nonempty_edge v
  let m := (hoFunctor.map (unitCommaFiberTarget (𝟙 (unitCommaFiber G x)) ≫ G)).toFunctor.map
    (SSet.Truncated.HomotopyCategory.homMk e)
  have h := unitCommaFiberArrowHom_naturality_edge G x e
  have := huA
  have := hvA
  have : IsIso (unitCommaFiberArrowHom G x u ≫ m) := h ▸ hvA
  have hm : IsIso m := by
    have hf : inv (unitCommaFiberArrowHom G x u) ≫
        (unitCommaFiberArrowHom G x u ≫ m) = m := by simp
    exact hf ▸ (inferInstance : IsIso (inv (unitCommaFiberArrowHom G x u) ≫
      (unitCommaFiberArrowHom G x u ≫ m)))
  let π := SerrePositivity.InfinityCategories.F1B.unitCommaFiberProjection G x
  have hmap : IsInvertibleEdge
      ((e.map ((truncation 2).map π)).map ((truncation 2).map G)) := by
    change IsIso m
    exact hm
  have he : IsInvertibleEdge e := leftFibration_reflects_invertibleEdge π e
    (hG.reflects_isInvertibleEdge (e.map ((truncation 2).map π)) hmap)
  exact hu.of_vertexIso (asIso (SSet.Truncated.HomotopyCategory.homMk e))

/-- 同じ comma の実矢印と始対象性の比較。 -/
lemma unitCommaFiber_isInitial_iff_invertibleArrow {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X) (hG : IsFullyFaithful G)
    (x : X _⦋0⦌) (u : (unitCommaFiber G x) _⦋0⦌) (hu : IsInitialVertex u)
    (huA : IsIso (unitCommaFiberArrowHom G x u))
    (v : (unitCommaFiber G x) _⦋0⦌) :
    IsInitialVertex v ↔ IsIso (unitCommaFiberArrowHom G x v) := by
  constructor
  · intro hv
    obtain ⟨e⟩ := hu.nonempty_edge v
    have he : IsInvertibleEdge e :=
      CategoryTheory.Limits.isIso_of_isInitial hu.isInitialHo hv.isInitialHo _
    have := huA
    rw [unitCommaFiberArrowHom_naturality_edge G x e]
    infer_instance
  · exact unitCommaFiber_isInitial_of_invertibleArrow G hG x u hu huA v
end SerrePositivity.InfinityCategories
