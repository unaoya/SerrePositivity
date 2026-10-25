module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSourceTerminalPushoutFiber
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.PushoutSpanBaseCoordinates
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CosliceFiberVertices
public import SerrePositivity.InfinityCategories.Stable.SuspensionSpanComparison
public import SerrePositivity.InfinityCategories.Stable.UniverseHorns
public import SerrePositivity.InfinityCategories.Core.ColimitExistenceTransfer

/-!
概要：固定始域の閉包内射圏の終対象の終域は、元の生成族に対して局所的である。
方針：任意の元の写像を pushout し、その指定 fiber を上辺の retraction 空間へ移す。
規約：終対象の存在はなお仮定する。高次の局所性は元の全写像空間について証明する。
使われ方：HTT 5.5.5.14 の終対象から局所対象への工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

private lemma terminal_edgeMappingFiber_of_pushout
    (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s)
    {a b : C _⦋0⦌} (f : C.Edge a b) (hf : f.edge ∈ generatedEdges edges)
    (g : (coconeMappingSpace (SSet.yonedaEquiv.symm a)
      ((generatedSourceTarget edges x).app _ s)) _⦋0⦌) :
    ∀ (R : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ C), IsPushoutSquare R →
    squareBottomEdge ≫ R = SSet.yonedaEquiv.symm f.edge →
    squareLeftEdge ≫ R = SSet.yonedaEquiv.symm (cosliceFiberVertexToEdge g).edge →
    horn₂₀.ι₀₁ ≫ pushoutSpan R = SSet.yonedaEquiv.symm f.edge →
    IsContractibleKan (vertexFiber (edgeCosliceSourceMapping f
      ((generatedSourceTarget edges x).app _ s)) g) := by
  intro R hR hRf hRg hraw
  let y := (generatedSourceTarget edges x).app _ s
  let v := cosliceFiberVertexToEdge g
  have hbottom : SSet.yonedaEquiv (squareBottomEdge ≫ R) ∈ generatedEdges edges := by
    rw [hRf]
    exact ((SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).apply_symm_apply f.edge).symm ▸ hf
  have hpoint : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ (squareLeftEdge ≫ R)) = y := by
    rw [hRg, stdSimplex.yonedaEquiv_δ_comp]
    exact ((congrArg (C.δ 0)
      ((SSet.yonedaEquiv (X := C) (n := ⦋1⦌)).apply_symm_apply v.edge))).trans v.tgt_eq
  have hy := squareLeftEdge_target_of_edge R v hRg
  let d := edgeTerminalMappingPointAt (squareLeftEdge ≫ R) y hpoint
  have hd := generatedSource_terminal_pushout_sourceFiber_contractible edges x s hs R
    hR hbottom hy d
    (edgeTerminalMappingPointAt_target_val (squareLeftEdge ≫ R) y hpoint)
  exact edgeCosliceSourceMapping_contractible_of_raw f y _ hraw _ hd g
    (pushoutSpanRightBase_terminal_of_edgeFiber R g hRg hpoint)

/-- 元の任意の閉包内辺の前合成は、終対象の終域への全ての指定基点で可縮 fiber を持つ。 -/
lemma generatedSource_terminal_edgeMappingFiber_contractible
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s)
    {a b : C _⦋0⦌} (f : C.Edge a b) (hf : f.edge ∈ generatedEdges edges)
    (g : (coconeMappingSpace (SSet.yonedaEquiv.symm a)
      ((generatedSourceTarget edges x).app _ s)) _⦋0⦌) :
    IsContractibleKan (vertexFiber (edgeCosliceSourceMapping f
      ((generatedSourceTarget edges x).app _ s)) g) := by
  let y := (generatedSourceTarget edges x).app _ s
  let v := cosliceFiberVertexToEdge g
  let p := edgeSpan f.toTruncated v.toTruncated
  let j := (uliftHornIso.{u, u + 1} 2 0).hom
  have hp : HasColimit p := by
    apply (F1B.kanHasColimit_iff_restrict_of_isIso p j).mpr
    exact hC (horn 2 0 : SSet.{u}) (j ≫ p)
  obtain ⟨c, hc⟩ := hp
  let R := coconeSquare c
  have hRf : squareBottomEdge ≫ R = SSet.yonedaEquiv.symm f.edge := by
    rw [coconeSquare_bottom, edgeSpan_left]
    rfl
  have hRg : squareLeftEdge ≫ R = SSet.yonedaEquiv.symm v.edge := by
    rw [coconeSquare_left, edgeSpan_right]
    rfl
  have hraw : horn₂₀.ι₀₁ ≫ pushoutSpan R = SSet.yonedaEquiv.symm f.edge := by
    rw [coconeSquare_span, edgeSpan_left]
    rfl
  exact terminal_edgeMappingFiber_of_pushout edges x s hs f hf g R
    (coconeSquare_isPushout c hc) hRf hRg hraw

/-- 元の閉包内辺への局所性は、零次元に限らず全写像空間について成立する。 -/
lemma generatedSource_terminal_edge_isLocalForHom
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s)
    {a b : C _⦋0⦌} (f : C.Edge a b) (hf : f.edge ∈ generatedEdges edges) :
    IsLocalForHom (Truncated.HomotopyCategory.homMk f.toTruncated)
      ((generatedSourceTarget edges x).app _ s) := by
  apply isLocalForHom_of_coslice_mapping_contractible f
  intro g
  exact isContractibleKan_of_iso (edgeCosliceSourceMappingFiberIso f
    ((generatedSourceTarget edges x).app _ s) g)
    (generatedSource_terminal_edgeMappingFiber_contractible hC edges x s hs f hf g)

/-- 終対象の終域は、元の強飽和生成閉包の全辺に対する局所対象である。 -/
lemma generatedSource_terminal_target_isLocalObject_generated
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s) :
    IsLocalObject (generatedEdges edges) ((generatedSourceTarget edges x).app _ s) := by
  intro e he
  exact generatedSource_terminal_edge_isLocalForHom hC edges x s hs
    (SSet.Edge.ofTruncated (edgeOfSimplex e)) he

/-- 終対象の終域は、最初に指定された小さい生成族に対する局所対象である。 -/
lemma generatedSource_terminal_target_isLocalObject
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    (s : (generatedSourceCategory edges x) _⦋0⦌) (hs : IsTerminalVertex s) :
    IsLocalObject (Set.range edges) ((generatedSourceTarget edges x).app _ s) :=
  isLocalObject_of_subset (subset_stronglySaturatedClosure _ _)
    (generatedSource_terminal_target_isLocalObject_generated hC edges x s hs)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
