module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationAugmentationDiagonals
public import SerrePositivity.InfinityCategories.DGNerve.DataLowDimensionalPullback

/-! # 閉 augmentation 側面の生成三角形と高次成分

概要：標準閉射に沿う側面の二三角形を取り出し、その次数 −1 成分を照合する。
方針：切断補正和を二単体で評価し、標準正規化射の primitive の零性を使う。
規約：実単体と全三辺を変更せず、側面全体の一致には三辺の照合も別途行う。
使われ方：元の固定辺へ戻す単位側面の補正。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (A B : DGFunctorCommaObject R E E (DGFunctor.id E))
  (k : ForgetEnrichment.of (Complex R) A ⟶ ForgetEnrichment.of (Complex R) B)
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)

def dgGluingClosedAugmentationTriangle (i : Fin 2) : Simplex R E 2 :=
  if i = 0 then
    dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      ((dgClosedEdge R Q k).edge.pullback (SimplexCategory.σ (1 : Fin 2)).toOrderHom)
      (SimplexCategory.σ (0 : Fin 2)).toOrderHom
  else
    dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      ((dgClosedEdge R Q k).edge.pullback (SimplexCategory.σ (0 : Fin 2)).toOrderHom)
      (SimplexCategory.σ (1 : Fin 2)).toOrderHom

private lemma dgGluingClosedAugmentationTriangle_high_zero₀ : HEq
    (dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      ((dgClosedEdge R Q k).edge.pullback
        (SimplexCategory.σ (1 : Fin 2)).toOrderHom)
      (SimplexCategory.σ (0 : Fin 2)).toOrderHom).triangleHom
    (0 : GradedHom R A.replacement B.source (-1)) := by
  let s := (dgClosedEdge R Q k).edge.pullback
    (SimplexCategory.σ (1 : Fin 2)).toOrderHom
  let β := (SimplexCategory.σ (0 : Fin 2)).toOrderHom
  have he := dgCommaAugmentationPrismData_hom_mixed R E E (DGFunctor.id E) s.toSimplexData
    β Finset.univ 0 2 (-1) (by decide) (by decide) (by decide) (by decide) rfl rfl
  have hs : s.hom Finset.univ 0 2 (-1)
      (by decide) (by decide) (by decide) (by decide) = 0 := by
    apply SimplexData.pullback_hom_of_not_inj
    · intro h
      have hh : (1 : Fin 3) = 2 := h (by decide) (by decide) rfl
      exact (by decide : (1 : Fin 3) ≠ 2) hh
    · decide
  have hm : dgCommaAugmentationPrismMixedHom R E E (DGFunctor.id E) s.toSimplexData
      β Finset.univ 0 2 (-1) (by decide) (by decide) (by decide) (by decide) = 0 := by
    unfold dgCommaAugmentationPrismMixedHom
    rw [hs, map_zero, compose_zero, zero_add]
    apply Finset.sum_eq_zero
    intro j hj
    split_ifs with h
    · have hlow : (0 : ℕ) < j.val.val := h.1
      have hhigh : j.val.val < (2 : ℕ) := h.2.1
      have hjv : j.val = (1 : Fin 3) := by
        apply Fin.ext
        change j.val.val = 1
        omega
      have hβ : β j.val = 0 := by rw [hjv]; rfl
      exact False.elim ((by decide : (0 : Fin 2) ≠ 1) (hβ.symm.trans h.2.2))
    · rfl
  exact he.trans (heq_of_eq hm)

private lemma dgGluingClosedAugmentationTriangle_high_zero₁
    (hp : dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E) A B 0
  (closedHomEquiv R (DGFunctorCommaObject R E E (DGFunctor.id E))
    (ForgetEnrichment.of (Complex R) A) (ForgetEnrichment.of (Complex R) B) k).val = 0) : HEq
    (dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      ((dgClosedEdge R Q k).edge.pullback
        (SimplexCategory.σ (0 : Fin 2)).toOrderHom)
      (SimplexCategory.σ (1 : Fin 2)).toOrderHom).triangleHom
    (0 : GradedHom R A.replacement B.source (-1)) := by
  let f := (dgClosedEdge R Q k).edge
  let α := (SimplexCategory.σ (0 : Fin 2)).toOrderHom
  let s := f.pullback α
  let β := (SimplexCategory.σ (1 : Fin 2)).toOrderHom
  let δ := (SimplexCategory.δ (0 : Fin 3)).toOrderHom
  have hindex : α.comp δ = OrderHom.id := by
    ext i
    fin_cases i <;> rfl
  have hres : s.toSimplexData.pullback δ = f.toSimplexData := by
    change (f.toSimplexData.pullback α).pullback δ = _
    rw [SimplexData.pullback_comp, hindex, SimplexData.pullback_id]
  have hfr := SimplexData.edgeHom_heq_of_pullback_eq s.toSimplexData f.toSimplexData δ
    (Fin.succAboveOrderEmb (0 : Fin 3)).injective hres 0 1 (by decide) (by decide)
  change HEq (s.edgeHom 1 2 (by decide)) (f.edgeHom 0 1 (by decide)) at hfr
  have hz : dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E) A B 0
      (s.edgeHom 1 2 (by decide)) = 0 := by
    rw [eq_of_heq hfr]
    exact hp
  have he := dgCommaAugmentationPrismData_hom_mixed R E E (DGFunctor.id E) s.toSimplexData
    β Finset.univ 0 2 (-1) (by decide) (by decide) (by decide) (by decide) rfl rfl
  have hs : s.hom Finset.univ 0 2 (-1)
      (by decide) (by decide) (by decide) (by decide) = 0 := by
    apply SimplexData.pullback_hom_of_not_inj
    · intro h
      have hh : (0 : Fin 3) = 1 := h (by decide) (by decide) rfl
      exact (by decide : (0 : Fin 3) ≠ 1) hh
    · decide
  have hm : dgCommaAugmentationPrismMixedHom R E E (DGFunctor.id E) s.toSimplexData
      β Finset.univ 0 2 (-1) (by decide) (by decide) (by decide) (by decide) = 0 := by
    unfold dgCommaAugmentationPrismMixedHom
    rw [hs, map_zero, compose_zero, zero_add]
    apply Finset.sum_eq_zero
    intro j hj
    split_ifs with h
    · have hlow : (0 : ℕ) < j.val.val := h.1
      have hhigh : j.val.val < (2 : ℕ) := h.2.1
      have hjv : j.val = (1 : Fin 3) := by
        apply Fin.ext
        change j.val.val = 1
        omega
      rcases j with ⟨j, hj⟩
      dsimp at hjv
      subst j
      unfold dgCommaAugmentationPrismCut
      change (_ : ℤˣ) • compose R (x := A.replacement) (y := A.replacement) (z := B.source)
        (dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E) A B 0
          (s.edgeHom 1 2 (by decide))) (_ : GradedHom R A.replacement A.replacement 0)
        (add_zero (-1)) = 0
      rw [hz, zero_compose, smul_zero]
    · rfl
  exact he.trans (heq_of_eq hm)

lemma dgGluingClosedAugmentationTriangle_high_zero
    (hp : dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E) A B 0
      (closedHomEquiv R Q (ForgetEnrichment.of (Complex R) A)
        (ForgetEnrichment.of (Complex R) B) k).val = 0) (i : Fin 2) :
    HEq (dgGluingClosedAugmentationTriangle R E A B k i).triangleHom
      (0 : GradedHom R A.replacement B.source (-1)) := by
  fin_cases i <;> dsimp [dgGluingClosedAugmentationTriangle]
  · exact dgGluingClosedAugmentationTriangle_high_zero₀ R E A B k
  · exact dgGluingClosedAugmentationTriangle_high_zero₁ R E A B k hp

variable (X : DGFunctorCommaObject R E E (DGFunctor.id E))
local notation "NX" => dgGluingIdentityCommaObject R E X.replacement
local notation "NY" => dgGluingIdentityCommaObject R E X.source

lemma dgGluingNormalizationInAugmentationTriangle_high_zero (i : Fin 2) :
    HEq (dgGluingClosedAugmentationTriangle R E NX X
      (dgGluingIdentityCommaNormalizationClosedIn R E X) i).triangleHom
      (0 : GradedHom R X.replacement X.source (-1)) := by
  exact dgGluingClosedAugmentationTriangle_high_zero R E NX X
    (dgGluingIdentityCommaNormalizationClosedIn R E X)
    (dgGluingNormalizationInAugmentationPrimitive_zero R E X) i

lemma dgGluingNormalizationOutAugmentationTriangle_high_zero (i : Fin 2) :
    HEq (dgGluingClosedAugmentationTriangle R E X NY
      (dgGluingIdentityCommaNormalizationClosedOut R E X) i).triangleHom
      (0 : GradedHom R X.replacement X.source (-1)) := by
  exact dgGluingClosedAugmentationTriangle_high_zero R E X NY
    (dgGluingIdentityCommaNormalizationClosedOut R E X)
    (dgGluingNormalizationOutAugmentationPrimitive_zero R E X) i

end SerrePositivity.InfinityCategories
