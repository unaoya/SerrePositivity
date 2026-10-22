module
public import SerrePositivity.InfinityCategories.Stable.LoopEvaluationLifting
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus
/-!
概要：指定された実 loop 図式の切断から二つの評価の同値性を得る。
方針：相対境界を普遍 loop 錐へ持ち上げ、同じ切断の厳密な終点式を使う。
規約：安定性を仮定しない。使われ方：HA 1.4.2.27 の安定性判定の準備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
lemma loopDiagramEvaluation_target_trivialKanFibration_of_section (X : SSet.{u})
    [Quasicategory X] [HasZeroVertex X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X) :
    TrivialKanFibration (loopDiagramEvaluation X 1 1) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  cases n with
  | zero =>
    let v := s.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv b)
    have hv : (loopDiagramEvaluation X 1 1).app (Opposite.op ⦋0⦌) v =
        SSet.yonedaEquiv b :=
      ConcreteCategory.congr_hom (NatTrans.congr_app hs (Opposite.op ⦋0⦌))
        (SSet.yonedaEquiv b)
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

lemma loopDiagramSection_isQCatEquivalence {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X) : IsQCatEquivalence s := by
  let := loopDiagramEvaluation_target_trivialKanFibration_of_section X s hs
  have hp : IsQCatEquivalence (loopDiagramEvaluation X 1 1) :=
    (qCatEquivalenceOfTrivialKanFibration (loopDiagramEvaluation X 1 1)).isQCatEquivalence
  apply hp.cancel_right
  rw [hs]
  exact (QCatEquivalence.refl X).isQCatEquivalence
lemma loopDiagramEvaluation_source_isQCatEquivalence_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) :
    IsQCatEquivalence (loopDiagramEvaluation X 0 0) :=
  (loopDiagramSection_isQCatEquivalence s hs).cancel_left hΩ
def loopDiagramFamilyIso_of_section {A X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (f g : A ⟶ loopDiagrams X)
    (h : f ≫ loopDiagramEvaluation X 1 1 = g ≫ loopDiagramEvaluation X 1 1) :
    FunctorIso f g := by
  let := loopDiagramEvaluation_target_trivialKanFibration_of_section X s hs
  exact functorIsoOfTrivialKanFibration (loopDiagramEvaluation X 1 1) f g h
end SerrePositivity.InfinityCategories
