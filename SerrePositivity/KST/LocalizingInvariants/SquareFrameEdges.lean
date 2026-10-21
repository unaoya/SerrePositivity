module

public import SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy
public import SerrePositivity.KST.LocalizingInvariants.ArrowIsoEndpointControl
public import SerrePositivity.InfinityCategories.F1B.ReflectiveLocalization

/-!
概要：端点を共有する指定四辺から境界を作り、各辺の類の一致を全境界の変形へ移す。
方針：各辺で同じ恒等頂点 path を指定してホモトピーを作り、角の一致を厳密に保つ。
規約：正方形本体は選び直さず境界だけを変形する。使われ方：BF 合成二脚への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def squareFrameOfEdges {X : SSet.{u}} {x y x' z : X _⦋0⦌}
    (b : X.Edge x y) (t : X.Edge x' z) (l : X.Edge x x') (r : X.Edge y z) : SquareFrame X where
  bottom := SSet.yonedaEquiv.symm b.edge
  top := SSet.yonedaEquiv.symm t.edge
  left := SSet.yonedaEquiv.symm l.edge
  right := SSet.yonedaEquiv.symm r.edge
  lower_left := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, b.src_eq, l.src_eq]
  lower_right := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, b.tgt_eq, r.src_eq]
  upper_left := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, t.src_eq, l.tgt_eq]
  upper_right := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, t.tgt_eq, r.tgt_eq]

structure FixedEndpointHomotopy {X : SSet.{u}} {x y : X _⦋0⦌} (f g : X.Edge x y) where
  homotopy : SSet.Homotopy (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge)
  source : (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h =
    snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (SSet.Edge.id x).edge
  target : (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h =
    snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (SSet.Edge.id y).edge

lemma fixedEndpointHomotopy_nonempty {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (f g : X.Edge x y) (h : Truncated.HomotopyCategory.homMk f.toTruncated =
      Truncated.HomotopyCategory.homMk g.toTruncated) : Nonempty (FixedEndpointHomotopy f g) := by
  obtain ⟨H, h₀, h₁⟩ := exists_arrowHomotopy_of_homMk_comm f.toTruncated g.toTruncated
    (SSet.Edge.id x).toTruncated (SSet.Edge.id y).toTruncated (by
      simpa only [SSet.Edge.toTruncated_id, SSet.Truncated.HomotopyCategory.homMk_id,
        Category.comp_id, Category.id_comp] using h)
  exact ⟨⟨H, h₀, h₁⟩⟩

def fixedEndpointHomotopy {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (f g : X.Edge x y) (h : Truncated.HomotopyCategory.homMk f.toTruncated =
      Truncated.HomotopyCategory.homMk g.toTruncated) : FixedEndpointHomotopy f g :=
  (fixedEndpointHomotopy_nonempty f g h).some

lemma FixedEndpointHomotopy.invertible {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {f g : X.Edge x y} (H : FixedEndpointHomotopy f g)
    (v : (Δ[1] : SSet.{u}) _⦋0⦌) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge H.homotopy v).toTruncated := by
  have hi : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy H.homotopy) :=
    arrowHomotopy_isInvertible_of_endpointPaths H.homotopy
      (SSet.Edge.id x).toTruncated (SSet.Edge.id y).toTruncated
      (by
        change IsIso (Truncated.HomotopyCategory.homMk (SSet.Edge.id x).toTruncated)
        rw [SSet.Edge.toTruncated_id, Truncated.HomotopyCategory.homMk_id]
        infer_instance)
      (by
        change IsIso (Truncated.HomotopyCategory.homMk (SSet.Edge.id y).toTruncated)
        rw [SSet.Edge.toTruncated_id, Truncated.HomotopyCategory.homMk_id]
        infer_instance)
      H.source H.target
  have : IsIso (Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy H.homotopy)) := hi
  exact homotopy_component_isInvertible_of_isIso H.homotopy v

end SerrePositivity.KST.LocalizingInvariants
