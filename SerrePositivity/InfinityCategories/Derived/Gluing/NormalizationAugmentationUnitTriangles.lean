module
public import SerrePositivity.InfinityCategories.Derived.Gluing.SimplexTriangleExt
/-! # 標準正規化側面の単位退化

概要：標準正規化の両側面を、元 augmentation の二つの退化三角形へ同定する。
方針：三辺と三点係数を別々に照合し、実二単体の外延性でまとめる。
規約：二つの生成三角形の両方を保持し、元 augmentation の端点を変えない。
使われ方：共有面と標準合成三角形を貼り合わせ、元の固定辺へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
private lemma dgGluingIdentityCommaAugmentationTarget :
    dgCommaAugmentationTarget R E E (DGFunctor.id E) =
    dgFunctorCommaSource R E E (DGFunctor.id E) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _
private lemma dgGluingClosedIdentityEdgeOfUnit (x : E) :
    (dgClosedEdge R E (𝟙 (ForgetEnrichment.of (Complex R) x))).edge =
    Simplex.ofEdge (fun _ : Fin 2 => x) (unitElement R x) := by
  apply Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    rfl
variable (X : DGFunctorCommaObject R E E (DGFunctor.id E))
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "NX" => dgGluingIdentityCommaObject R E X.replacement
local notation "NY" => dgGluingIdentityCommaObject R E X.source
private lemma dgGluingNormalizationInSourceEdge :
    (dgClosedEdge R Q (dgGluingIdentityCommaNormalizationClosedIn R E X)).edge.map
      (dgCommaAugmentationSource R E E (DGFunctor.id E)) =
      Simplex.ofEdge (fun _ : Fin 2 => X.replacement) (unitElement R X.replacement) := by
  rw [dgClosedEdge_map]
  change (dgClosedEdge R E ((dgFunctorCommaReplacement R E E (DGFunctor.id E)).onClosed.map
    (dgGluingIdentityCommaNormalizationClosedIn R E X))).edge = _
  rw [dgGluingIdentityCommaNormalizationClosedIn_replacement, dgGluingClosedIdentityEdgeOfUnit]
private lemma dgGluingNormalizationInTargetEdge :
    (dgClosedEdge R Q (dgGluingIdentityCommaNormalizationClosedIn R E X)).edge.map
      (dgCommaAugmentationTarget R E E (DGFunctor.id E)) =
      (dgClosedEdge R E X.augmentation).edge := by
  rw [dgGluingIdentityCommaAugmentationTarget, dgClosedEdge_map,
    dgGluingIdentityCommaNormalizationClosedIn_source]
private lemma dgGluingNormalizationOutSourceEdge :
    (dgClosedEdge R Q (dgGluingIdentityCommaNormalizationClosedOut R E X)).edge.map
      (dgCommaAugmentationSource R E E (DGFunctor.id E)) =
      (dgClosedEdge R E X.augmentation).edge := by
  rw [dgClosedEdge_map]
  change (dgClosedEdge R E ((dgFunctorCommaReplacement R E E (DGFunctor.id E)).onClosed.map
    (dgGluingIdentityCommaNormalizationClosedOut R E X))).edge = _
  rw [dgGluingIdentityCommaNormalizationClosedOut_replacement]
private lemma dgGluingNormalizationOutTargetEdge :
    (dgClosedEdge R Q (dgGluingIdentityCommaNormalizationClosedOut R E X)).edge.map
      (dgCommaAugmentationTarget R E E (DGFunctor.id E)) =
      Simplex.ofEdge (fun _ : Fin 2 => X.source) (unitElement R X.source) := by
  rw [dgGluingIdentityCommaAugmentationTarget, dgClosedEdge_map,
    dgGluingIdentityCommaNormalizationClosedOut_source, dgGluingClosedIdentityEdgeOfUnit]


private lemma dgGluingDegenerateTriangleFace (s : Simplex R E 1) (k : Fin 2) (j : Fin 3) :
    (s.pullback (SimplexCategory.σ k).toOrderHom).pullback
      (SimplexCategory.δ j).toOrderHom =
    if k=0 ∧ j=2 then
      Simplex.ofEdge (fun _ : Fin 2 => s.obj 0) (unitElement R (s.obj 0))
    else if k=1 ∧ j=0 then
      Simplex.ofEdge (fun _ : Fin 2 => s.obj 1) (unitElement R (s.obj 1)) else s := by
  have hi : (SimplexCategory.σ k).toOrderHom.comp
      (SimplexCategory.δ j).toOrderHom =
      if k=0 ∧ j=2 then OrderHom.const (Fin 2) (0 : Fin 2)
      else if k=1 ∧ j=0 then OrderHom.const (Fin 2) (1 : Fin 2) else OrderHom.id := by
    fin_cases k <;> fin_cases j <;> norm_num
    all_goals ext l; fin_cases l <;> rfl
  rw [Simplex.pullback_comp, hi]
  fin_cases k <;> fin_cases j <;> norm_num
  all_goals first
    | exact dgGluingSimplexConstantEdgePullback R E s _
    | exact Simplex.pullback_id s

private lemma dgGluingDegenerateTriangleHigh (s : Simplex R E 1) (k : Fin 2) :
    HEq (s.pullback (SimplexCategory.σ k).toOrderHom).triangleHom
      (0 : GradedHom R (s.obj 0) (s.obj 1) (-1)) := by
  fin_cases k
  all_goals apply heq_of_eq
  all_goals apply SimplexData.pullback_hom_of_not_inj
  · intro h
    have hh : (0 : Fin 3) = 1 := h (by decide) (by decide) rfl
    exact (by decide : (0 : Fin 3) ≠ 1) hh
  · decide
  · intro h
    have hh : (1 : Fin 3) = 2 := h (by decide) (by decide) rfl
    exact (by decide : (1 : Fin 3) ≠ 2) hh
  · decide

lemma dgGluingNormalizationInAugmentationTriangle_eq (i : Fin 2) :
    dgGluingClosedAugmentationTriangle R E NX X
      (dgGluingIdentityCommaNormalizationClosedIn R E X) i =
    (dgClosedEdge R E X.augmentation).edge.pullback
      (SimplexCategory.σ (0 : Fin 2)).toOrderHom := by
  apply dgGluingTriangle_faces_ext R E
  · funext j
    fin_cases i <;> fin_cases j <;> rfl
  · intro j
    rw [dgGluingDegenerateTriangleFace]
    fin_cases i <;> fin_cases j <;> norm_num
    · rw [dgGluingClosedAugmentationTriangle_zero_last]
    · rw [dgGluingClosedAugmentationTriangle_diagonal,
        dgGluingNormalizationInAugmentationDiagonal_eq]
    · rw [dgGluingClosedAugmentationTriangle_zero_first, dgGluingNormalizationInSourceEdge]
      rfl
    · rw [dgGluingClosedAugmentationTriangle_one_last, dgGluingNormalizationInTargetEdge]
    · rw [dgGluingClosedAugmentationTriangle_diagonal,
        dgGluingNormalizationInAugmentationDiagonal_eq]
    · rw [dgGluingClosedAugmentationTriangle_one_first]
      change (dgClosedEdge R E (𝟙 (ForgetEnrichment.of (Complex R) X.replacement))).edge = _
      exact dgGluingClosedIdentityEdgeOfUnit R E _
  · exact (dgGluingNormalizationInAugmentationTriangle_high_zero R E X i).trans
      (dgGluingDegenerateTriangleHigh R E (dgClosedEdge R E X.augmentation).edge 0).symm

lemma dgGluingNormalizationOutAugmentationTriangle_eq (i : Fin 2) :
    dgGluingClosedAugmentationTriangle R E X NY
      (dgGluingIdentityCommaNormalizationClosedOut R E X) i =
    (dgClosedEdge R E X.augmentation).edge.pullback
      (SimplexCategory.σ (1 : Fin 2)).toOrderHom := by
  apply dgGluingTriangle_faces_ext R E
  · funext j
    fin_cases i <;> fin_cases j <;> rfl
  · intro j
    rw [dgGluingDegenerateTriangleFace]
    fin_cases i <;> fin_cases j <;> norm_num
    · rw [dgGluingClosedAugmentationTriangle_zero_last]
      exact dgGluingClosedIdentityEdgeOfUnit R E _
    · rw [dgGluingClosedAugmentationTriangle_diagonal,
        dgGluingNormalizationOutAugmentationDiagonal_eq]
    · rw [dgGluingClosedAugmentationTriangle_zero_first, dgGluingNormalizationOutSourceEdge]
    · rw [dgGluingClosedAugmentationTriangle_one_last, dgGluingNormalizationOutTargetEdge]
      rfl
    · rw [dgGluingClosedAugmentationTriangle_diagonal,
        dgGluingNormalizationOutAugmentationDiagonal_eq]
    · rw [dgGluingClosedAugmentationTriangle_one_first]
  · exact (dgGluingNormalizationOutAugmentationTriangle_high_zero R E X i).trans
      (dgGluingDegenerateTriangleHigh R E (dgClosedEdge R E X.augmentation).edge 1).symm
end SerrePositivity.InfinityCategories
