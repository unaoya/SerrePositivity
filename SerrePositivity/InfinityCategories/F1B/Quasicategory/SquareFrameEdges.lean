module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Core.ArrowSquareHomotopy
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.HomotopyInvertibility
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrameBoundary
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.F1B.Localization.ReflectiveLocalization
public import SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowIsoEndpointControl

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.F1B.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

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

end SerrePositivity.InfinityCategories.F1B.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.fixedEndpointHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedEndpointHomotopy := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.fixedEndpointHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedEndpointHomotopy_nonempty := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.fixedEndpointHomotopy_nonempty

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.squareFrameOfEdges (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.squareFrameOfEdges := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.squareFrameOfEdges

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy.casesOn := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy.ctorIdx := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.homotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy.homotopy := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.homotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy.invertible := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.invertible

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy.mk := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy.noConfusion := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy.noConfusionType := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy.rec := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy.recOn := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy.source := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy.target := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.squareFrameOfEdges._proof_1 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.squareFrameOfEdges._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.squareFrameOfEdges._proof_2 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.squareFrameOfEdges._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.squareFrameOfEdges._proof_3 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.squareFrameOfEdges._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.squareFrameOfEdges._proof_4 := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.squareFrameOfEdges._proof_4

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy.mk.inj := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy.mk.injEq := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FixedEndpointHomotopy.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.FixedEndpointHomotopy.mk.sizeOf_spec
