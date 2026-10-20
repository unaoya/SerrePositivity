module
public import SerrePositivity.KST.LocalizingInvariants.CofiberDiagramChoices

/-!
概要：安定圏の普遍 cofiber 四角形の右辺評価は trivial Kan fibration。
方針：元の右辺を保ち、零始点の上辺と普遍錐を境界に沿って充填する。
規約：引き戻しを元の cofiber 図式へ安定性で戻す。使われ方：cofiber 回転の完全性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams

/- 右辺を固定したまま全境界を持ち上げる。 -/
instance right_trivialKanFibration (X : SSet.{u})
    [Quasicategory X] [IsStable X] :
    TrivialKanFibration (right X) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  cases n with
  | zero =>
    obtain ⟨v, hv⟩ := right_surjective X (SSet.yonedaEquiv b)
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm v
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, hv]
  | succ n =>
    let ι := (fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
      Predicate).ι
    let j := (fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj X) IsZeroSourceArrow).ι
    have hBR : CommSq (a ≫ top X) (boundary (n + 1)).ι
        (zeroSourceArrowTarget X)
        (b ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
      constructor
      rw [Category.assoc, ← right_target, ← Category.assoc, sq.w, Category.assoc]
    have := TrivialKanFibration.mem (p := zeroSourceArrowTarget X)
      (boundary (n + 1)).ι inferInstance
    let R := hBR.lift
    have hLR : b ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        (R ≫ j) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
      hBR.fac_right.symm
    let d := stable_cospanFamilyOfArrows b (R ≫ j) hLR
    have hd : (boundary (n + 1)).ι ≫ d = a ≫ ι ≫ (pre cospanSquareBoundary).app X := by
      apply stable_cospanFamily_hom_ext
      · rw [Category.assoc, stable_cospanFamilyOfArrows_left]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
          cospanSquareBoundary_rightEdge]
        change (boundary (n + 1)).ι ≫ b = a ≫ right X
        exact sq.w.symm
      · rw [Category.assoc, stable_cospanFamilyOfArrows_right]
        rw [← Category.assoc, hBR.fac_left, Category.assoc]
        rw [top, fullSubcomplexLift_ι]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, cospanSquareBoundary_topEdge]
        rfl
    let c := a ≫ cones X
    have hcd : CommSq c (boundary (n + 1)).ι
        (limitConeProjection (horn 2 2 : SSet.{u}) X) d := by
      constructor
      rw [Category.assoc, cones_projection]
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
      change a ≫ (cones X ≫ k) ≫
        (pre cospanConeSquareIso.inv).app X = _
      rw [cones_inclusion]
      simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id,
        pre_id, NatTrans.id_app, Category.comp_id]
      rfl
    have hv (v : (Δ[n + 1] : SSet.{u}) _⦋0⦌) :
        Predicate (F.app (Opposite.op ⦋0⦌) v) := by
      let w : (boundary (n + 1) : SSet.{u}) _⦋0⦌ := ⟨v, by
        have h := vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
        rw [Equiv.symm_apply_apply] at h
        exact h⟩
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app hFa (Opposite.op ⦋0⦌)) w
      change F.app (Opposite.op ⦋0⦌) v = (a.app (Opposite.op ⦋0⦌) w).val at he
      rw [he]
      exact fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) w)
    let g := fullSubcomplexLift Predicate F hv
    have hg : g ≫ ι = F := fullSubcomplexLift_ι _ _ _
    refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
    · apply (cancel_mono ι).1
      rw [Category.assoc, hg, hFa]
    · change g ≫ ι ≫ (pre squareRightEdge).app X = b
      rw [← Category.assoc, hg]
      have hFd : F ≫ (pre cospanSquareBoundary).app X = d := by
        dsimp only [F]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map]
        have hi : cospanSquareBoundary ≫ cospanConeSquareIso.inv =
            joinInr Δ[0] (horn 2 2 : SSet.{u}) := by
          simp only [cospanSquareBoundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        rw [hi]
        exact hcd.fac_right
      have hFL : F ≫ (pre squareRightEdge).app X = b := by
        have hh := congrArg (fun t ↦ t ≫ (pre horn₂₂.ι₀₂).app X) hFd
        rw [Category.assoc, stable_cospanFamilyOfArrows_left] at hh
        simpa only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
          cospanSquareBoundary_rightEdge] using hh
      exact hFL

end SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
