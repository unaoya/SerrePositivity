module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.SimplexTriangleExt
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
private lemma dgGluingIdentityCommaAugmentationTarget :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R E E (DGFunctor.id E) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R E E (DGFunctor.id E) := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
  intro x y
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _
private lemma dgGluingClosedIdentityEdgeOfUnit (x : E) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (𝟙 (ForgetEnrichment.of (Complex R) x))).edge =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (fun _ : Fin 2 => x) (unitElement R x) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    rfl
variable (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "NX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement
local notation "NY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.source
private lemma dgGluingNormalizationInSourceEdge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R Q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X)).edge.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (fun _ : Fin 2 => X.replacement) (unitElement R X.replacement) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R E E (DGFunctor.id E)).onClosed.map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X))).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn_replacement, dgGluingClosedIdentityEdgeOfUnit]
private lemma dgGluingNormalizationInTargetEdge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R Q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X)).edge.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R E E (DGFunctor.id E)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E X.augmentation).edge := by
  rw [dgGluingIdentityCommaAugmentationTarget, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn_source]
private lemma dgGluingNormalizationOutSourceEdge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R Q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E X)).edge.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E X.augmentation).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R E E (DGFunctor.id E)).onClosed.map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E X))).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut_replacement]
private lemma dgGluingNormalizationOutTargetEdge :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R Q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E X)).edge.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R E E (DGFunctor.id E)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (fun _ : Fin 2 => X.source) (unitElement R X.source) := by
  rw [dgGluingIdentityCommaAugmentationTarget, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut_source, dgGluingClosedIdentityEdgeOfUnit]


private lemma dgGluingDegenerateTriangleFace (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E 1) (k : Fin 2) (j : Fin 3) :
    (s.pullback (SimplexCategory.σ k).toOrderHom).pullback
      (SimplexCategory.δ j).toOrderHom =
    if k=0 ∧ j=2 then
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (fun _ : Fin 2 => s.obj 0) (unitElement R (s.obj 0))
    else if k=1 ∧ j=0 then
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (fun _ : Fin 2 => s.obj 1) (unitElement R (s.obj 1)) else s := by
  have hi : (SimplexCategory.σ k).toOrderHom.comp
      (SimplexCategory.δ j).toOrderHom =
      if k=0 ∧ j=2 then OrderHom.const (Fin 2) (0 : Fin 2)
      else if k=1 ∧ j=0 then OrderHom.const (Fin 2) (1 : Fin 2) else OrderHom.id := by
    fin_cases k <;> fin_cases j <;> norm_num
    all_goals ext l; fin_cases l <;> rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp, hi]
  fin_cases k <;> fin_cases j <;> norm_num
  all_goals first
    | exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSimplexConstantEdgePullback R E s _
    | exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_id s

private lemma dgGluingDegenerateTriangleHigh (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E 1) (k : Fin 2) :
    HEq (s.pullback (SimplexCategory.σ k).toOrderHom).triangleHom
      (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj 0) (s.obj 1) (-1)) := by
  fin_cases k
  all_goals apply heq_of_eq
  all_goals apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj
  · intro h
    have hh : (0 : Fin 3) = 1 := h (by decide) (by decide) rfl
    exact (by decide : (0 : Fin 3) ≠ 1) hh
  · decide
  · intro h
    have hh : (1 : Fin 3) = 2 := h (by decide) (by decide) rfl
    exact (by decide : (1 : Fin 3) ≠ 2) hh
  · decide

lemma dgGluingNormalizationInAugmentationTriangle_eq (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle R E NX X
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X) i =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E X.augmentation).edge.pullback
      (SimplexCategory.σ (0 : Fin 2)).toOrderHom := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangle_faces_ext R E
  · funext j
    fin_cases i <;> fin_cases j <;> rfl
  · intro j
    rw [dgGluingDegenerateTriangleFace]
    fin_cases i <;> fin_cases j <;> norm_num
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle_zero_last]
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle_diagonal,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationInAugmentationDiagonal_eq]
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle_zero_first, dgGluingNormalizationInSourceEdge]
      rfl
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle_one_last, dgGluingNormalizationInTargetEdge]
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle_diagonal,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationInAugmentationDiagonal_eq]
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle_one_first]
      change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (𝟙 (ForgetEnrichment.of (Complex R) X.replacement))).edge = _
      exact dgGluingClosedIdentityEdgeOfUnit R E _
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationInAugmentationTriangle_high_zero R E X i).trans
      (dgGluingDegenerateTriangleHigh R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E X.augmentation).edge 0).symm

lemma dgGluingNormalizationOutAugmentationTriangle_eq (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle R E X NY
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E X) i =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E X.augmentation).edge.pullback
      (SimplexCategory.σ (1 : Fin 2)).toOrderHom := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangle_faces_ext R E
  · funext j
    fin_cases i <;> fin_cases j <;> rfl
  · intro j
    rw [dgGluingDegenerateTriangleFace]
    fin_cases i <;> fin_cases j <;> norm_num
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle_zero_last]
      exact dgGluingClosedIdentityEdgeOfUnit R E _
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle_diagonal,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationOutAugmentationDiagonal_eq]
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle_zero_first, dgGluingNormalizationOutSourceEdge]
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle_one_last, dgGluingNormalizationOutTargetEdge]
      rfl
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle_diagonal,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationOutAugmentationDiagonal_eq]
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingClosedAugmentationTriangle_one_first]
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationOutAugmentationTriangle_high_zero R E X i).trans
      (dgGluingDegenerateTriangleHigh R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E X.augmentation).edge 1).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
