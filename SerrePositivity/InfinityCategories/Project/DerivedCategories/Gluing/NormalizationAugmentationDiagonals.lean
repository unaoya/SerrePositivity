module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NormalizationAugmentationTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCochainElement

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet CochainComplex HomComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "NX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement
local notation "NY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.source

lemma dgGluingNormalizationInAugmentationDiagonal_coefficient :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R Q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X)).edge
      OrderHom.id).edgeHom 0 1 (by decide))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R E E (DGFunctor.id E) X).val := by
  let s := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R Q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X)).edge
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_hom_mixed R E E (DGFunctor.id E) s.toSimplexData
    OrderHom.id {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide) rfl rfl
  have hm := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom_two R E E (DGFunctor.id E) s.toSimplexData
    OrderHom.id {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hn := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R E E (DGFunctor.id E)).closedHomEquiv_map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn_replacement] at hn
  have hs : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E)).map (s.obj 0) (s.obj 1)).f 0
      (s.hom {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide)) =
      (_root_.SerrePositivity.DifferentialGraded.unitElement R X.replacement).val := by
    exact (congrArg Subtype.val hn).symm
  rw [hs] at hm
  exact he.trans (heq_of_eq (hm.trans (_root_.SerrePositivity.DifferentialGraded.compose_unit R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R E E (DGFunctor.id E) X).val)))

lemma dgGluingNormalizationOutAugmentationDiagonal_coefficient :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R Q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E X)).edge
      OrderHom.id).edgeHom 0 1 (by decide))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R E E (DGFunctor.id E) X).val := by
  let s := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R Q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E X)).edge
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismData_hom_mixed R E E (DGFunctor.id E) s.toSimplexData
    OrderHom.id {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide) rfl rfl
  have hm := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom_two R E E (DGFunctor.id E) s.toSimplexData
    OrderHom.id {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hn := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R E E (DGFunctor.id E)).closedHomEquiv_map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E X)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut_replacement] at hn
  have hs : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E)).map (s.obj 0) (s.obj 1)).f 0
      (s.hom {0, 1} 0 1 0 (by decide) (by decide) (by decide) (by decide)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R E E (DGFunctor.id E) X).val := by
    exact (congrArg Subtype.val hn).symm
  rw [hs] at hm
  change _ = _root_.SerrePositivity.DifferentialGraded.compose R (x := X.replacement) (y := X.source) (z := X.source)
    (_root_.SerrePositivity.DifferentialGraded.unitElement R X.source).val
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R E E (DGFunctor.id E) X).val (add_zero 0) at hm
  exact he.trans (heq_of_eq (hm.trans (_root_.SerrePositivity.DifferentialGraded.unit_compose R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationComponent R E E (DGFunctor.id E) X).val)))

lemma dgGluingNormalizationInAugmentationDiagonal_eq :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R Q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X)).edge
      OrderHom.id = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E X.augmentation).edge := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact eq_of_heq (dgGluingNormalizationInAugmentationDiagonal_coefficient R E X)

lemma dgGluingNormalizationOutAugmentationDiagonal_eq :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R Q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E X)).edge
      OrderHom.id = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E X.augmentation).edge := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeEquiv.injective
  refine Sigma.ext ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact eq_of_heq (dgGluingNormalizationOutAugmentationDiagonal_coefficient R E X)

lemma dgGluingNormalizationInAugmentationPrimitive_zero :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E) NX X 0
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R Q (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) NX) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X)).val = 0 := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) NX X).v 0 (-1) rfl
    (cycleFromUnit _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationIn R E X)).val = 0
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCochainElement (homObject R E X.replacement X.source))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationIn_primitive R E X)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCochainElement, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    ModuleCat.comp_apply, Cochain.zero_v, ModuleCat.hom_zero, LinearMap.zero_apply] at h
  convert h using 1 <;> rfl

lemma dgGluingNormalizationOutAugmentationPrimitive_zero :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E) X NY 0
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R Q (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) X) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) NY)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E X)).val = 0 := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) X NY).v 0 (-1) rfl
    (cycleFromUnit _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationOut R E X)).val = 0
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCochainElement (homObject R E X.replacement X.source))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationOut_primitive R E X)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCochainElement, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    ModuleCat.comp_apply, Cochain.zero_v, ModuleCat.hom_zero, LinearMap.zero_apply] at h
  convert h using 1 <;> rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
