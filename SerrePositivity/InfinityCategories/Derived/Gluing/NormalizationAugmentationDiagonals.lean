module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationAugmentationTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitCochainElement

/-! # 標準正規化側面の対角辺

概要：標準閉射へ augmentation を適用した側面の対角は、元の augmentation に一致する。
方針：前側は恒等射の右単位律、後側は恒等射の左単位律で係数を照合する。
規約：実単体そのものの等式を保持し、Small 仮定や高次成分の一致を仮定しない。
使われ方：側面の三角形を単位補正として扱う際に、共通対角を固定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet CochainComplex HomComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]
  (X : DGFunctorCommaObject R E E (DGFunctor.id E))
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "NX" => dgGluingIdentityCommaObject R E X.replacement
local notation "NY" => dgGluingIdentityCommaObject R E X.source

lemma dgGluingNormalizationInAugmentationDiagonal_coefficient :
    HEq ((dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      (dgClosedEdge R Q (dgGluingIdentityCommaNormalizationClosedIn R E X)).edge
      OrderHom.id).edgeHom 0 1 (by decide))
      (dgCommaAugmentationComponent R E E (DGFunctor.id E) X).val := by
  let s := (dgClosedEdge R Q (dgGluingIdentityCommaNormalizationClosedIn R E X)).edge
  have he := dgCommaAugmentationPrismData_hom_mixed R E E (DGFunctor.id E) s.toSimplexData
    OrderHom.id {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide) rfl rfl
  have hm := dgCommaAugmentationPrismMixedHom_two R E E (DGFunctor.id E) s.toSimplexData
    OrderHom.id {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hn := (dgFunctorCommaReplacement R E E (DGFunctor.id E)).closedHomEquiv_map
    (dgGluingIdentityCommaNormalizationClosedIn R E X)
  rw [dgGluingIdentityCommaNormalizationClosedIn_replacement] at hn
  have hs : ((dgCommaAugmentationSource R E E (DGFunctor.id E)).map (s.obj 0) (s.obj 1)).f 0
      (s.hom {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide)) =
      (unitElement R X.replacement).val := by
    exact (congrArg Subtype.val hn).symm
  rw [hs] at hm
  exact he.trans (heq_of_eq (hm.trans (compose_unit R
    (dgCommaAugmentationComponent R E E (DGFunctor.id E) X).val)))

lemma dgGluingNormalizationOutAugmentationDiagonal_coefficient :
    HEq ((dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      (dgClosedEdge R Q (dgGluingIdentityCommaNormalizationClosedOut R E X)).edge
      OrderHom.id).edgeHom 0 1 (by decide))
      (dgCommaAugmentationComponent R E E (DGFunctor.id E) X).val := by
  let s := (dgClosedEdge R Q (dgGluingIdentityCommaNormalizationClosedOut R E X)).edge
  have he := dgCommaAugmentationPrismData_hom_mixed R E E (DGFunctor.id E) s.toSimplexData
    OrderHom.id {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide) rfl rfl
  have hm := dgCommaAugmentationPrismMixedHom_two R E E (DGFunctor.id E) s.toSimplexData
    OrderHom.id {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hn := (dgFunctorCommaReplacement R E E (DGFunctor.id E)).closedHomEquiv_map
    (dgGluingIdentityCommaNormalizationClosedOut R E X)
  rw [dgGluingIdentityCommaNormalizationClosedOut_replacement] at hn
  have hs : ((dgCommaAugmentationSource R E E (DGFunctor.id E)).map (s.obj 0) (s.obj 1)).f 0
      (s.hom {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide)) =
      (dgCommaAugmentationComponent R E E (DGFunctor.id E) X).val := by
    exact (congrArg Subtype.val hn).symm
  rw [hs] at hm
  change _ = compose R (x := X.replacement) (y := X.source) (z := X.source)
    (unitElement R X.source).val
    (dgCommaAugmentationComponent R E E (DGFunctor.id E) X).val (add_zero 0) at hm
  exact he.trans (heq_of_eq (hm.trans (unit_compose R
    (dgCommaAugmentationComponent R E E (DGFunctor.id E) X).val)))

lemma dgGluingNormalizationInAugmentationDiagonal_eq :
    dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      (dgClosedEdge R Q (dgGluingIdentityCommaNormalizationClosedIn R E X)).edge
      OrderHom.id = (dgClosedEdge R E X.augmentation).edge := by
  apply Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact eq_of_heq (dgGluingNormalizationInAugmentationDiagonal_coefficient R E X)

lemma dgGluingNormalizationOutAugmentationDiagonal_eq :
    dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      (dgClosedEdge R Q (dgGluingIdentityCommaNormalizationClosedOut R E X)).edge
      OrderHom.id = (dgClosedEdge R E X.augmentation).edge := by
  apply Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact eq_of_heq (dgGluingNormalizationOutAugmentationDiagonal_coefficient R E X)

lemma dgGluingNormalizationInAugmentationPrimitive_zero :
    dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E) NX X 0
    (closedHomEquiv R Q (ForgetEnrichment.of (Complex R) NX) (ForgetEnrichment.of (Complex R) X)
      (dgGluingIdentityCommaNormalizationClosedIn R E X)).val = 0 := by
  change (dgFunctorCommaPrimitive R E E (DGFunctor.id E) NX X).v 0 (-1) rfl
    (cycleFromUnit _ (dgGluingIdentityCommaNormalizationIn R E X)).val = 0
  have h := congrArg (dgGluingUnitCochainElement (homObject R E X.replacement X.source))
    (dgGluingIdentityCommaNormalizationIn_primitive R E X)
  simp only [dgGluingUnitCochainElement, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    ModuleCat.comp_apply, Cochain.zero_v, ModuleCat.hom_zero, LinearMap.zero_apply] at h
  convert h using 1 <;> rfl

lemma dgGluingNormalizationOutAugmentationPrimitive_zero :
    dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E) X NY 0
    (closedHomEquiv R Q (ForgetEnrichment.of (Complex R) X) (ForgetEnrichment.of (Complex R) NY)
      (dgGluingIdentityCommaNormalizationClosedOut R E X)).val = 0 := by
  change (dgFunctorCommaPrimitive R E E (DGFunctor.id E) X NY).v 0 (-1) rfl
    (cycleFromUnit _ (dgGluingIdentityCommaNormalizationOut R E X)).val = 0
  have h := congrArg (dgGluingUnitCochainElement (homObject R E X.replacement X.source))
    (dgGluingIdentityCommaNormalizationOut_primitive R E X)
  simp only [dgGluingUnitCochainElement, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    ModuleCat.comp_apply, Cochain.zero_v, ModuleCat.hom_zero, LinearMap.zero_apply] at h
  convert h using 1 <;> rfl

end SerrePositivity.InfinityCategories
