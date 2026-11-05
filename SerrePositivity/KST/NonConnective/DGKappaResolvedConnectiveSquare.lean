module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedRelativeRoof
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionConnectiveStructure

/-!
概要：D-9 の実核と Sp-6 の固定零化構成子を、ν の Verdier 認証なしで接続する。
方針：元の指定収縮付き合成から同じ四辺を持つ固定 dg 四角形を選び、頂点を回収する。
規約：固定 ν の Verdier 証拠は要求しない。K 零角の接続だけは明示した Perf 零性に条件付き。
使われ方：K-7 c5 の一般経路で同じ実核・平坦 cone・懸垂・元の商包含を保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective

variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v))
  [DGCategory R D] [Small.{u} D] {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 元の商合成の指定収縮を D 正本の存在定理から選ぶ。 -/
def dgKappaResolvedKernelContraction :=
  (dgKappaResolvedKernel_exists_contracted R D I).choose

/-- 選んだ指定収縮の元の dg 関手は、同じ実包含と商の合成そのもの。 -/
theorem dgKappaResolvedKernelContraction_functor :
    (dgKappaResolvedKernelContraction R D I).toDGFunctor =
      (dgKappaResolvedKernelInputMap R D I).down.comp
        (dgKappaResolvedSuspensionInputMap R D I).down :=
  (dgKappaResolvedKernel_exists_contracted R D I).choose_spec

/-- 同じ実核・分解 cone・懸垂を含む、固定 dg 入力内の元の零化四角形。 -/
def dgKappaResolvedConnectiveSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶
      dgKInputInfinity.{u, max (u + 1) v} R :=
  (exists_dgFixedNullSquare R (dgKappaResolvedKernelInputMap R D I)
    (dgKappaResolvedSuspensionInputMap R D I) (dgKappaResolvedKernelContraction R D I)
    (dgKappaResolvedKernelContraction_functor R D I)).choose

/-- 元の包含と商の全一単体は、同じ零化四角形の下辺・右辺に厳密に残る。 -/
theorem dgKappaResolvedConnectiveSquare_edges :
    squareBottomEdge ≫ dgKappaResolvedConnectiveSquare R D I =
      SSet.yonedaEquiv.symm (coherentNerveEdge (dgKappaResolvedKernelInputMap R D I)).edge ∧
    squareRightEdge ≫ dgKappaResolvedConnectiveSquare R D I =
      SSet.yonedaEquiv.symm (coherentNerveEdge (dgKappaResolvedSuspensionInputMap R D I)).edge ∧
    squareLeftEdge ≫ dgKappaResolvedConnectiveSquare R D I =
      SSet.yonedaEquiv.symm (coherentNerveEdge
        (dgFixedNullLeft R (A := dgKappaResolvedKernelKInput R D I))).edge := by
  have h := (exists_dgFixedNullSquare R (dgKappaResolvedKernelInputMap R D I)
    (dgKappaResolvedSuspensionInputMap R D I) (dgKappaResolvedKernelContraction R D I)
    (dgKappaResolvedKernelContraction_functor R D I)).choose_spec
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- 実核・平坦 cone・懸垂・全対象商の四頂点は、元の同じ入力頂点である。 -/
theorem dgKappaResolvedConnectiveSquare_vertices :
    squareVertex (dgKappaResolvedConnectiveSquare R D I) 0 0 =
      coherentNerveVertex (dgKappaResolvedKernelKInput R D I) ∧
    squareVertex (dgKappaResolvedConnectiveSquare R D I) 1 0 =
      coherentNerveVertex (dgKappaResolvedConeKInput R D I) ∧
    squareVertex (dgKappaResolvedConnectiveSquare R D I) 1 1 =
      coherentNerveVertex (dgKappaSuspensionKInput R D I) ∧
    squareVertex (dgKappaResolvedConnectiveSquare R D I) 0 1 =
      coherentNerveVertex (dgFixedNullInput R (dgKappaResolvedKernelKInput R D I)) := by
  obtain ⟨hi, hq, hl⟩ := dgKappaResolvedConnectiveSquare_edges R D I
  let ie : (dgKInputInfinity.{u, max (u + 1) v} R).Edge
      (coherentNerveVertex (dgKappaResolvedKernelKInput R D I))
      (coherentNerveVertex (dgKappaResolvedConeKInput R D I)) :=
    coherentNerveEdge (dgKappaResolvedKernelInputMap R D I)
  let qe : (dgKInputInfinity.{u, max (u + 1) v} R).Edge
      (coherentNerveVertex (dgKappaResolvedConeKInput R D I))
      (coherentNerveVertex (dgKappaSuspensionKInput R D I)) :=
    coherentNerveEdge (dgKappaResolvedSuspensionInputMap R D I)
  let le : (dgKInputInfinity.{u, max (u + 1) v} R).Edge
      (coherentNerveVertex (dgKappaResolvedKernelKInput R D I))
      (coherentNerveVertex (dgFixedNullInput R (dgKappaResolvedKernelKInput R D I))) :=
    coherentNerveEdge (dgFixedNullLeft R (A := dgKappaResolvedKernelKInput R D I))
  change squareBottomEdge ≫ _ = SSet.yonedaEquiv.symm ie.edge at hi
  change squareRightEdge ≫ _ = SSet.yonedaEquiv.symm qe.edge at hq
  change squareLeftEdge ≫ _ = SSet.yonedaEquiv.symm le.edge at hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := squareBottomEdge_source (dgKappaResolvedConnectiveSquare R D I)
    rw [hi, Equiv.apply_symm_apply, ie.src_eq] at h
    exact h.symm
  · have h := squareBottomEdge_target (dgKappaResolvedConnectiveSquare R D I)
    rw [hi, Equiv.apply_symm_apply, ie.tgt_eq] at h
    exact h.symm
  · have h := squareRightEdge_target (dgKappaResolvedConnectiveSquare R D I)
    rw [hq, Equiv.apply_symm_apply, qe.tgt_eq] at h
    exact h.symm
  · have h := squareLeftEdge_target (dgKappaResolvedConnectiveSquare R D I)
    rw [hl, Equiv.apply_symm_apply, le.tgt_eq] at h
    exact h.symm

/-- 実全対象商の Perf 零性に条件付きで、同じ元の固定 K 四角形の零角を得る。 -/
theorem dgKappaResolvedConnectiveSquare_zero_corner
    (hz : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.IsZeroCategory (dgKInputStableValue R
      (dgFixedNullInput R (dgKappaResolvedKernelKInput R D I)))) :
    IsZeroVertex (squareVertex (dgKappaResolvedConnectiveSquare R D I ≫ dgKInputK R) 0 1) := by
  change IsZeroVertex ((dgKInputK R).app (Opposite.op ⦋0⦌)
    (squareVertex (dgKappaResolvedConnectiveSquare R D I) 0 1))
  rw [(dgKappaResolvedConnectiveSquare_vertices R D I).2.2.2]
  exact dgKInputK_vertex_isZero_of_zero R _ hz

end SerrePositivity.KST.NonConnective
