module
public import SerrePositivity.InfinityCategories.F1.SuspensionDiagramArrows

/-! # Suspension 図式の始点評価の境界充填

概要：安定 ∞ 圏の suspension 図式の始点評価は trivial Kan fibration。
方針：入力の二辺を零対象へ向かう辺として延長し、普遍余錐の相対境界充填で四角形を延長する。
規約：正次元では全頂点の零角と普遍性を境界から継承する。
使われ方：S3 の Σ の関手性と選択の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：suspension 図式の始点評価は全境界を持ち上げる。
方針：二本の零終点の辺を持ち上げ、span の族を貼り、普遍余錐として四角形を充填する。
規約：安定 ∞ 圏を仮定する。
使われ方：h C 上の suspension 関手とその選択の自然性。 -/
instance suspensionDiagramEvaluation_source_trivialKanFibration (X : SSet.{u})
    [Quasicategory X] [IsStable X] :
    TrivialKanFibration (suspensionDiagramEvaluation X 0 0) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  cases n with
  | zero =>
    obtain ⟨v, hv⟩ := suspensionDiagramEvaluation_source_surjective X (SSet.yonedaEquiv b)
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm v
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, hv]
  | succ n =>
    let ι := (fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
      IsSuspensionDiagramVertex).ι
    let j := (fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj X) IsZeroTargetArrow).ι
    have hBL : CommSq (a ≫ suspensionDiagramBottomArrow X) (boundary (n + 1)).ι
        (zeroTargetArrowSource X) b := by
      constructor
      rw [Category.assoc, suspensionDiagramBottomArrow_source]
      exact sq.w
    have hBR : CommSq (a ≫ suspensionDiagramLeftArrow X) (boundary (n + 1)).ι
        (zeroTargetArrowSource X) b := by
      constructor
      rw [Category.assoc, suspensionDiagramLeftArrow_source]
      exact sq.w
    have := TrivialKanFibration.mem (p := zeroTargetArrowSource X)
      (boundary (n + 1)).ι inferInstance
    let L := hBL.lift
    let R := hBR.lift
    have hLR : (L ≫ j) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        (R ≫ j) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
      hBL.fac_right.trans hBR.fac_right.symm
    let d := stable_spanFamilyOfArrows (L ≫ j) (R ≫ j) hLR
    have hd : (boundary (n + 1)).ι ≫ d = a ≫ ι ≫ (pre spanSquareBoundary).app X := by
      apply stable_spanFamily_hom_ext
      · rw [Category.assoc, stable_spanFamilyOfArrows_left]
        rw [← Category.assoc, hBL.fac_left, Category.assoc]
        rw [suspensionDiagramBottomArrow, fullSubcomplexLift_ι]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, spanSquareBoundary_bottomEdge]
        rfl
      · rw [Category.assoc, stable_spanFamilyOfArrows_right]
        rw [← Category.assoc, hBR.fac_left, Category.assoc]
        rw [suspensionDiagramLeftArrow, fullSubcomplexLift_ι]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, spanSquareBoundary_leftEdge]
        rfl
    let c := a ≫ suspensionDiagramCoconeFamily X
    have hcd : CommSq c (boundary (n + 1)).ι
        (colimitCoconeProjection (horn 2 0 : SSet.{u}) X) d := by
      constructor
      rw [Category.assoc, suspensionDiagramCoconeFamily_projection]
      exact hd.symm
    have : HasLiftingProperty (boundary (n + 1)).ι
        (colimitCoconeProjection (horn 2 0 : SSet.{u}) X) :=
      relativeInitialProjection_hasLiftingProperty_boundary
        (coconeRestriction (horn 2 0 : SSet.{u}) X) n
    let U := hcd.lift
    let k := (relativeInitialVertices (coconeRestriction (horn 2 0 : SSet.{u}) X)).ι
    let F := U ≫ k ≫ (pre spanCoconeSquareIso.inv).app X
    have hFa : (boundary (n + 1)).ι ≫ F = a ≫ ι := by
      dsimp only [F]
      rw [← Category.assoc, ← Category.assoc, hcd.fac_left, Category.assoc]
      change a ≫ (suspensionDiagramCoconeFamily X ≫ k) ≫
        (pre spanCoconeSquareIso.inv).app X = _
      rw [suspensionDiagramCoconeFamily_ι]
      simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id,
        pre_id, NatTrans.id_app, Category.comp_id]
      rfl
    have hv (v : (Δ[n + 1] : SSet.{u}) _⦋0⦌) :
        IsSuspensionDiagramVertex (F.app (Opposite.op ⦋0⦌) v) := by
      let w : (boundary (n + 1) : SSet.{u}) _⦋0⦌ := ⟨v, by
        have h := vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
        rw [Equiv.symm_apply_apply] at h
        exact h⟩
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app hFa (Opposite.op ⦋0⦌)) w
      change F.app (Opposite.op ⦋0⦌) v = (a.app (Opposite.op ⦋0⦌) w).val at he
      rw [he]
      exact fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) w)
    let g := fullSubcomplexLift IsSuspensionDiagramVertex F hv
    have hg : g ≫ ι = F := fullSubcomplexLift_ι _ _ _
    refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
    · apply (cancel_mono ι).1
      rw [Category.assoc, hg, hFa]
    · change g ≫ ι ≫ evaluateFunctorAt
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = b
      rw [← Category.assoc, hg]
      have hFd : F ≫ (pre spanSquareBoundary).app X = d := by
        dsimp only [F]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map]
        have hi : spanSquareBoundary ≫ spanCoconeSquareIso.inv =
            joinInl (horn 2 0 : SSet.{u}) Δ[0] := by
          simp only [spanSquareBoundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        rw [hi]
        exact hcd.fac_right
      have hFL : F ≫ (pre squareBottomEdge).app X = L ≫ j := by
        have hh := congrArg (fun t ↦ t ≫ (pre horn₂₀.ι₀₁).app X) hFd
        rw [Category.assoc, stable_spanFamilyOfArrows_left] at hh
        simpa only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
          spanSquareBoundary_bottomEdge] using hh
      have hh := congrArg
        (fun t ↦ t ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) hFL
      rw [Category.assoc, stable_pre_evaluateFunctorAt] at hh
      exact hh.trans hBL.fac_right

end SerrePositivity.InfinityCategories
