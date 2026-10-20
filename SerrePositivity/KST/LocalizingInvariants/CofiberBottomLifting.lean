module
public import SerrePositivity.KST.LocalizingInvariants.CofiberDiagramChoices

/-!
概要：普遍 cofiber 四角形の底辺評価は trivial Kan fibration。
方針：元の底辺を保ち、零終点の左辺と普遍余錐を境界に沿って充填する。
規約：全高次単体と指定された底辺を保持する。使われ方：cofiber の完全な選択。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams

/- 底辺を固定したまま全境界を持ち上げる。 -/
instance bottom_trivialKanFibration (X : SSet.{u})
    [Quasicategory X] [IsStable X] :
    TrivialKanFibration (bottom X) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  cases n with
  | zero =>
    obtain ⟨v, hv⟩ := bottom_surjective X (SSet.yonedaEquiv b)
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm v
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, hv]
  | succ n =>
    let ι := (fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
      Predicate).ι
    let j := (fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj X) IsZeroTargetArrow).ι
    have hBR : CommSq (a ≫ left X) (boundary (n + 1)).ι
        (zeroTargetArrowSource X)
        (b ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
      constructor
      rw [Category.assoc, ← bottom_source, ← Category.assoc, sq.w, Category.assoc]
    have := TrivialKanFibration.mem (p := zeroTargetArrowSource X)
      (boundary (n + 1)).ι inferInstance
    let R := hBR.lift
    have hLR : b ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        (R ≫ j) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
      hBR.fac_right.symm
    let d := stable_spanFamilyOfArrows b (R ≫ j) hLR
    have hd : (boundary (n + 1)).ι ≫ d = a ≫ ι ≫ (pre spanSquareBoundary).app X := by
      apply stable_spanFamily_hom_ext
      · rw [Category.assoc, stable_spanFamilyOfArrows_left]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
          spanSquareBoundary_bottomEdge]
        change (boundary (n + 1)).ι ≫ b = a ≫ bottom X
        exact sq.w.symm
      · rw [Category.assoc, stable_spanFamilyOfArrows_right]
        rw [← Category.assoc, hBR.fac_left, Category.assoc]
        rw [left, fullSubcomplexLift_ι]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, spanSquareBoundary_leftEdge]
        rfl
    let c := a ≫ cocones X
    have hcd : CommSq c (boundary (n + 1)).ι
        (colimitCoconeProjection (horn 2 0 : SSet.{u}) X) d := by
      constructor
      rw [Category.assoc, cocones_projection]
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
      change a ≫ (cocones X ≫ k) ≫
        (pre spanCoconeSquareIso.inv).app X = _
      rw [cocones_inclusion]
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
    · change g ≫ ι ≫ (pre squareBottomEdge).app X = b
      rw [← Category.assoc, hg]
      have hFd : F ≫ (pre spanSquareBoundary).app X = d := by
        dsimp only [F]
        simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map]
        have hi : spanSquareBoundary ≫ spanCoconeSquareIso.inv =
            joinInl (horn 2 0 : SSet.{u}) Δ[0] := by
          simp only [spanSquareBoundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        rw [hi]
        exact hcd.fac_right
      have hFL : F ≫ (pre squareBottomEdge).app X = b := by
        have hh := congrArg (fun t ↦ t ≫ (pre horn₂₀.ι₀₁).app X) hFd
        rw [Category.assoc, stable_spanFamilyOfArrows_left] at hh
        simpa only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
          spanSquareBoundary_bottomEdge] using hh
      exact hFL

end SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
