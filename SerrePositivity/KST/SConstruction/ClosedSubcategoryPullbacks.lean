module
public import SerrePositivity.KST.SConstruction.ClosedSubcategoryZero
public import SerrePositivity.KST.SConstruction.ZeroCospanChoices

/-! # 閉じた全部分圏の零角付き引き戻し
概要：零角を持つ四角形の cospan の普遍補完を全部分圏へ戻し、引き戻しの保存を得る。
方針：零脚の cospan の極限と閉性を使い、内部の極限の一意性で任意の四角形へ移す。
規約：部分圏の安定性を仮定しない。使われ方：fiber と cofiber の一致の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 零角を持つ周囲の四角形の cospan を厳密に保持する引き戻し補完。 -/
lemma exists_pullbackSquare_of_zero_corner {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) (hz : IsZeroVertex (squareVertex F 0 1)) :
    ∃ R : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X,
      pullbackCospan R = pullbackCospan F ∧ IsPullbackSquare R := by
  have hp : IsZeroSourceArrow (functorVertex (horn₂₂.ι₁₂ ≫ pullbackCospan F)) := by
    unfold IsZeroSourceArrow
    rw [evaluateFunctorAt_functorVertex]
    change IsZeroVertex ((horn₂₂.ι₁₂ ≫ cospanSquareBoundary ≫ F).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    rw [← Category.assoc, cospanSquareBoundary_topEdge]
    exact hz
  obtain ⟨c, hc⟩ := hasLimit_zeroCospan (pullbackCospan F) hp
  let R := cospanConeSquareIso.inv ≫ c.val
  have hR : pullbackCospan R = pullbackCospan F := by
    dsimp only [R, pullbackCospan, cospanSquareBoundary]
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact c.property
  refine ⟨R, hR, ?_⟩
  apply (isLimitCone_iff_of_diagram_eq (c := pullbackCone R) (d := c) hR _).2 hc
  dsimp only [pullbackCone, R]
  exact Iso.hom_inv_id_assoc _ _

/-- 周囲で同じ cospan を持つ四角形の終点側の三つの角は頂点条件を満たす。 -/
lemma square_final_corners_of_cospan {X : StableModel.{u}} (P : ClosedStablePredicate X)
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ closedSubcategory P)
    (R : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X.carrier)
    (h : pullbackCospan R = pullbackCospan (F ≫ (fullSubcomplexOnVertices _ P.predicate).ι)) :
    P.predicate (squareVertex R 1 0) ∧ P.predicate (squareVertex R 0 1) ∧
      P.predicate (squareVertex R 1 1) := by
  have hr : squareRightEdge ≫ R =
      squareRightEdge ≫ F ≫ (fullSubcomplexOnVertices _ P.predicate).ι := by
    have he := congrArg (fun p => horn₂₂.ι₀₂ ≫ p) h
    simpa only [pullbackCospan, ← Category.assoc, cospanSquareBoundary_rightEdge] using he
  have ht : squareTopEdge ≫ R =
      squareTopEdge ≫ F ≫ (fullSubcomplexOnVertices _ P.predicate).ι := by
    have he := congrArg (fun p => horn₂₂.ι₁₂ ≫ p) h
    simpa only [pullbackCospan, ← Category.assoc, cospanSquareBoundary_topEdge] using he
  have h10 : squareVertex R 1 0 = (squareVertex F 1 0).val :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hr (Opposite.op ⦋0⦌))
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  have h11 : squareVertex R 1 1 = (squareVertex F 1 1).val :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hr (Opposite.op ⦋0⦌))
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  have h01 : squareVertex R 0 1 = (squareVertex F 0 1).val :=
    ConcreteCategory.congr_hom (NatTrans.congr_app ht (Opposite.op ⦋0⦌))
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  exact ⟨h10.symm ▸ closedSubcategory_vertex P _, h01.symm ▸ closedSubcategory_vertex P _,
    h11.symm ▸ closedSubcategory_vertex P _⟩

/-- 内部の零角付き cospan は周囲でも普遍な内部の引き戻し四角形へ補完できる。 -/
lemma exists_closedSubcategory_pullbackSquare {X : StableModel.{u}} (P : ClosedStablePredicate X)
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ closedSubcategory P)
    (hz : IsZeroVertex (squareVertex F 0 1)) :
    ∃ D : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ closedSubcategory P,
      pullbackCospan D = pullbackCospan F ∧ IsPullbackSquare D ∧
        IsPullbackSquare (D ≫ (fullSubcomplexOnVertices _ P.predicate).ι) := by
  let i := (fullSubcomplexOnVertices _ P.predicate).ι
  obtain ⟨R, hR, hRp⟩ := exists_pullbackSquare_of_zero_corner (F ≫ i)
    (closedSubcategoryInclusion_preservesZero P _ hz)
  have hc := square_final_corners_of_cospan P F R hR
  have hv := square_vertices_of_corners P.predicate R
    (P.pullback_mem R hRp hc.1 hc.2.1 hc.2.2) hc.1 hc.2.1 hc.2.2
  let D := fullSubcomplexLift P.predicate R hv
  have hDi : D ≫ i = R := fullSubcomplexLift_ι _ _ _
  have hDs : pullbackCospan D = pullbackCospan F := by
    apply (cancel_mono i).1
    change cospanSquareBoundary ≫ D ≫ i = cospanSquareBoundary ≫ F ≫ i
    rw [hDi]
    exact hR
  have hDp : IsPullbackSquare (D ≫ i) := hDi.symm ▸ hRp
  exact ⟨D, hDs, isPullbackSquare_fullSubcomplex_of_ambient P.predicate D hDp, hDp⟩

/-- 閉じた全部分圏の包含は零角付きの内部の引き戻しを保存する。 -/
lemma closedSubcategoryInclusion_preservesFiber {X : StableModel.{u}} (P : ClosedStablePredicate X)
    (t : ZeroTriangle (closedSubcategory P)) (ht : IsFiberSequence t) :
    IsPullbackSquare (t.square ≫ (fullSubcomplexOnVertices _ P.predicate).ι) := by
  let i := (fullSubcomplexOnVertices _ P.predicate).ι
  obtain ⟨D, hDs, hD, hDi⟩ := exists_closedSubcategory_pullbackSquare P t.square t.zero_corner
  let cD : JoinCone (pullbackCospan t.square) := ⟨(pullbackCone D).val,
    (pullbackCone D).property.trans hDs⟩
  have hcD : IsLimitCone cD :=
    (isLimitCone_iff_of_diagram_eq (c := cD) (d := pullbackCone D) hDs.symm rfl).2 hD
  have hcDi : IsLimitCone (mapJoinCone i cD) := by
    apply (isLimitCone_iff_of_diagram_eq (c := mapJoinCone i cD)
      (d := pullbackCone (D ≫ i)) _ _).2 hDi
    · exact congrArg (fun p => p ≫ i) hDs.symm
    · exact Category.assoc _ _ _
  let e := limitConeIso cD (pullbackCone t.square) hcD ht
  exact hcDi.of_vertexIso (VertexIso.map e (sliceOverPostcomp (pullbackCospan t.square) i))

end SerrePositivity.KST.SConstruction
