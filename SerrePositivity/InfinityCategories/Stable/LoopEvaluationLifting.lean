module
public import SerrePositivity.InfinityCategories.Stable.LoopDiagramArrows

/-! # Loop 図式の終点評価の境界充填

概要：安定 ∞ 圏の loop 図式の終点評価は trivial Kan fibration。
方針：入力の二辺を零対象から出る辺として延長し、普遍錐の相対境界充填で四角形を延長する。
規約：正次元では全頂点の零角と普遍性を境界から継承する。
使われ方：S3 の Ω の関手性と選択の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：loop 図式の終点評価は全境界を持ち上げる。
方針：二本の零終点の辺を持ち上げ、cospan の族を貼り、普遍錐として四角形を充填する。
規約：安定 ∞ 圏を仮定する。
使われ方：h C 上の loop 関手とその選択の自然性。 -/
instance loopDiagramEvaluation_target_trivialKanFibration (X : SSet.{u})
    [Quasicategory X] [IsStable X] :
    TrivialKanFibration (loopDiagramEvaluation X 1 1) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  cases n with
  | zero =>
    obtain ⟨v, hv⟩ := loopDiagramEvaluation_target_surjective X (SSet.yonedaEquiv b)
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm v
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, hv]
  | succ n =>
    let ι := (fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
      IsLoopDiagramVertex).ι
    let j := (fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj X) IsZeroSourceArrow).ι
    have hBL : CommSq (a ≫ loopDiagramRightArrow X) (boundary (n + 1)).ι
        (zeroSourceArrowTarget X) b := by
      constructor
      rw [Category.assoc, loopDiagramRightArrow_target]
      exact sq.w
    have hBR : CommSq (a ≫ loopDiagramTopArrow X) (boundary (n + 1)).ι
        (zeroSourceArrowTarget X) b := by
      constructor
      rw [Category.assoc, loopDiagramTopArrow_target]
      exact sq.w
    have := TrivialKanFibration.mem (p := zeroSourceArrowTarget X)
      (boundary (n + 1)).ι inferInstance
    let L := hBL.lift
    let R := hBR.lift
    have hLR : (L ≫ j) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        (R ≫ j) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
      hBL.fac_right.trans hBR.fac_right.symm
    let d := stable_cospanFamilyOfArrows (L ≫ j) (R ≫ j) hLR
    have hd : (boundary (n + 1)).ι ≫ d = a ≫ ι ≫ (pre cospanSquareBoundary).app X := by
      apply stable_cospanFamily_hom_ext
      · rw [Category.assoc, stable_cospanFamilyOfArrows_left]
        rw [← Category.assoc, hBL.fac_left, Category.assoc]
        rw [loopDiagramRightArrow, fullSubcomplexLift_ι]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, cospanSquareBoundary_rightEdge]
        rfl
      · rw [Category.assoc, stable_cospanFamilyOfArrows_right]
        rw [← Category.assoc, hBR.fac_left, Category.assoc]
        rw [loopDiagramTopArrow, fullSubcomplexLift_ι]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, cospanSquareBoundary_topEdge]
        rfl
    let c := a ≫ loopDiagramConeFamily X
    have hcd : CommSq c (boundary (n + 1)).ι
        (limitConeProjection (horn 2 2 : SSet.{u}) X) d := by
      constructor
      rw [Category.assoc, loopDiagramConeFamily_projection]
      exact hd.symm
    have : HasLiftingProperty (boundary (n + 1)).ι
        (limitConeProjection (horn 2 2 : SSet.{u}) X) :=
      relativeTerminalProjection_hasLiftingProperty_boundary
        (coneRestriction (horn 2 2 : SSet.{u}) X) n
    let U := hcd.lift
    let k := (relativeTerminalVertices (coneRestriction (horn 2 2 : SSet.{u}) X)).ι
    let F := U ≫ k ≫ (pre cospanConeSquareIso.inv).app X
    have hFa : (boundary (n + 1)).ι ≫ F = a ≫ ι := by
      dsimp only [F]
      rw [← Category.assoc, ← Category.assoc, hcd.fac_left, Category.assoc]
      change a ≫ (loopDiagramConeFamily X ≫ k) ≫
        (pre cospanConeSquareIso.inv).app X = _
      rw [loopDiagramConeFamily_ι]
      simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id,
        pre_id, NatTrans.id_app, Category.comp_id]
      rfl
    have hv (v : (Δ[n + 1] : SSet.{u}) _⦋0⦌) :
        IsLoopDiagramVertex (F.app (Opposite.op ⦋0⦌) v) := by
      let w : (boundary (n + 1) : SSet.{u}) _⦋0⦌ := ⟨v, by
        have h := vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
        rw [Equiv.symm_apply_apply] at h
        exact h⟩
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app hFa (Opposite.op ⦋0⦌)) w
      change F.app (Opposite.op ⦋0⦌) v = (a.app (Opposite.op ⦋0⦌) w).val at he
      rw [he]
      exact fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) w)
    let g := fullSubcomplexLift IsLoopDiagramVertex F hv
    have hg : g ≫ ι = F := fullSubcomplexLift_ι _ _ _
    refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
    · apply (cancel_mono ι).1
      rw [Category.assoc, hg, hFa]
    · change g ≫ ι ≫ evaluateFunctorAt
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = b
      rw [← Category.assoc, hg]
      have hFd : F ≫ (pre cospanSquareBoundary).app X = d := by
        dsimp only [F]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map]
        have hi : cospanSquareBoundary ≫ cospanConeSquareIso.inv =
            joinInr Δ[0] (horn 2 2 : SSet.{u}) := by
          simp only [cospanSquareBoundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        rw [hi]
        exact hcd.fac_right
      have hFL : F ≫ (pre squareRightEdge).app X = L ≫ j := by
        have hh := congrArg (fun t ↦ t ≫ (pre horn₂₂.ι₀₂).app X) hFd
        rw [Category.assoc, stable_cospanFamilyOfArrows_left] at hh
        simpa only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
          cospanSquareBoundary_rightEdge] using hh
      have hh := congrArg
        (fun t ↦ t ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) hFL
      rw [Category.assoc, stable_pre_evaluateFunctorAt] at hh
      exact hh.trans hBL.fac_right

end SerrePositivity.InfinityCategories
