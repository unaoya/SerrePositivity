module

public import SerrePositivity.InfinityCategories.F2.Idempotent.BicartesianZeroFamilies
public import SerrePositivity.InfinityCategories.F1.ColimitFullyFaithful

/-!
概要：元の双カルテジアン零角四角形の下辺射影は、正次元の全境界を持ち上げる。
方針：元の零枝を延長し、同じ span の普遍余錐の境界充填で全四角形を回収する。
規約：新しい辺の fiber/cofiber の存在や標的の安定性を仮定しない。
使われ方：下辺射影の充満忠実性と、完備化の新しい辺の双普遍四角形の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の下辺射影は、同じ元の全四角形の正次元境界を全て厳密に充填する。 -/
lemma bicartesianZeroBottomProjection_hasLiftingProperty_boundary (X : SSet.{u})
    [Quasicategory X] [HasZeroVertex X] (n : ℕ) :
    HasLiftingProperty (boundary (n + 1)).ι (bicartesianZeroBottomProjection X) := by
  constructor
  intro a b sq
  let ι := (fullSubcomplexOnVertices ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)
    IsBicartesianZeroVertex).ι
  let j := (fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj X) IsZeroTargetArrow).ι
  have hBR : CommSq (a ≫ bicartesianZeroLeftArrow X) (boundary (n + 1)).ι
      (zeroTargetArrowSource X)
      (b ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
    constructor
    rw [Category.assoc, bicartesianZeroLeftArrow_source, ← Category.assoc, sq.w, Category.assoc]
  have := TrivialKanFibration.mem (p := zeroTargetArrowSource X)
    (boundary (n + 1)).ι inferInstance
  let R := hBR.lift
  have hLR : b ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (R ≫ j) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := hBR.fac_right.symm
  let d := stable_spanFamilyOfArrows b (R ≫ j) hLR
  have hd : (boundary (n + 1)).ι ≫ d = a ≫ ι ≫ (pre spanSquareBoundary).app X := by
    apply stable_spanFamily_hom_ext
    · rw [Category.assoc, stable_spanFamilyOfArrows_left]
      simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, spanSquareBoundary_bottomEdge]
      exact sq.w.symm
    · rw [Category.assoc, stable_spanFamilyOfArrows_right]
      rw [← Category.assoc, hBR.fac_left, Category.assoc, bicartesianZeroLeftArrow_inclusion]
      simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, spanSquareBoundary_leftEdge]
      rfl
  let c := a ≫ bicartesianZeroCoconeMap X
  have hcd : CommSq c (boundary (n + 1)).ι
      (colimitCoconeProjection (horn 2 0 : SSet.{u}) X) d := by
    constructor
    rw [Category.assoc, bicartesianZeroCoconeMap_projection]
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
    change a ≫ (bicartesianZeroCoconeMap X ≫ k) ≫
      (pre spanCoconeSquareIso.inv).app X = _
    rw [bicartesianZeroCoconeMap_inclusion]
    simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map, Iso.inv_hom_id,
      pre_id, NatTrans.id_app, Category.comp_id]
    rfl
  have hv (v : (Δ[n + 1] : SSet.{u}) _⦋0⦌) :
      IsBicartesianZeroVertex (F.app (Opposite.op ⦋0⦌) v) := by
    let w : (boundary (n + 1) : SSet.{u}) _⦋0⦌ := ⟨v, by
      have h := vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
      rw [Equiv.symm_apply_apply] at h
      exact h⟩
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app hFa (Opposite.op ⦋0⦌)) w
    change F.app (Opposite.op ⦋0⦌) v = (a.app (Opposite.op ⦋0⦌) w).val at he
    rw [he]
    exact fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) w)
  let g := fullSubcomplexLift IsBicartesianZeroVertex F hv
  have hg : g ≫ ι = F := fullSubcomplexLift_ι _ _ _
  refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
  · apply (cancel_mono ι).mp
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
    have hh := congrArg (fun t ↦ t ≫ (pre horn₂₀.ι₀₁).app X) hFd
    rw [Category.assoc, stable_spanFamilyOfArrows_left] at hh
    simpa only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
      spanSquareBoundary_bottomEdge] using hh

/-- 元の下辺射影は全写像空間で充満忠実。標的の安定性は不要。 -/
lemma bicartesianZeroBottomProjection_isFullyFaithful (X : SSet.{u})
    [Quasicategory X] [HasZeroVertex X] : IsFullyFaithful (bicartesianZeroBottomProjection X) :=
  isFullyFaithful_of_boundary_succ _ (bicartesianZeroBottomProjection_hasLiftingProperty_boundary X)

end SerrePositivity.InfinityCategories.F2.Idempotent
