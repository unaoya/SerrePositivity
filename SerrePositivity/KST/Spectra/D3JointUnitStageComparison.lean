module

public import SerrePositivity.KST.Spectra.D3PointedKanPreIsoAlgebra
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoPrecompEndpointTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoPrecompCompositionValue

/-!
概要：共同単位比較の角制限を、以前の同じ実面の指定単位比較へ接続する。
方針：全関手空間での段制限・逆射保存と、等式由来の端点正規化だけを合成する。
規約：単位子や比較の選択を変えない。保持済み模型補正との一致は別途証明する。
使われ方：全パラメータ共同模型比較から既存実面模型比較への指定値の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
open EnrichedOrderedCylinder
local instance d3UnitStageSquareCategory : SmallCategory (Fin 2 × Fin 2) :=
  Preorder.smallCategory (Fin 2 × Fin 2)

/-- 共同左単位の段制限は、同じ元の実面単位比較に端点表示を除いて一致する。 -/
lemma d3DoubleEndpointLeftTargetParameter_stage (k l : Fin 2) :
    HEq ((d3ParameterPreFunctorIso d3DoubleEndpointLeftTargetParameterIso.{u}).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stageInclusion (C := PointedKanObject.{u}) (k, l))))
      (d3DoubleEndpointLeftTargetIso k l) := by
  have hs := d3ParameterPreFunctorIso_stage d3DoubleEndpointLeftTargetParameterIso.{u} (k, l)
  have hn := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm.trans (heq_of_eq hs)
  have hu : HEq (d3PointedKanPreFunctorIso
      (d3DoubleEndpointLeftTargetParameterIso.{u}.hom.app (Opposite.op (k, l))))
      (d3PointedKanPreFunctorIso (λ_ (d3EndpointParameterObj.{u} (k, l))).hom) := by
    simp only [d3DoubleEndpointLeftTargetParameterIso_hom_app]
    rfl
  have hi : d3PointedKanPreFunctorIso (λ_ (d3EndpointParameterObj.{u} (k, l))).hom =
      (d3PointedKanPreFunctorIso (λ_ (d3EndpointParameterObj.{u} (k, l))).inv).symm := by
    rw [d3PointedKanPreFunctorIso_inv, Iso.symm_symm_eq]
  exact hn.trans (hu.trans ((heq_of_eq hi).trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm))

/-- 共同右単位についても、以前の同じ実面比較の指定値を回収する。 -/
lemma d3DoubleEndpointRightTargetParameter_stage (k l : Fin 2) :
    HEq ((d3ParameterPreFunctorIso d3DoubleEndpointRightTargetParameterIso.{u}).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stageInclusion (C := PointedKanObject.{u}) (k, l))))
      (d3DoubleEndpointRightTargetIso k l) := by
  have hs := d3ParameterPreFunctorIso_stage d3DoubleEndpointRightTargetParameterIso.{u} (k, l)
  have hn := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm.trans (heq_of_eq hs)
  have hu : HEq (d3PointedKanPreFunctorIso
      (d3DoubleEndpointRightTargetParameterIso.{u}.hom.app (Opposite.op (k, l))))
      (d3PointedKanPreFunctorIso (ρ_ (d3EndpointParameterObj.{u} (k, l))).hom) := by
    simp only [d3DoubleEndpointRightTargetParameterIso_hom_app]
    rfl
  have hi : d3PointedKanPreFunctorIso (ρ_ (d3EndpointParameterObj.{u} (k, l))).hom =
      (d3PointedKanPreFunctorIso (ρ_ (d3EndpointParameterObj.{u} (k, l))).inv).symm := by
    rw [d3PointedKanPreFunctorIso_inv, Iso.symm_symm_eq]
  exact hn.trans (hu.trans ((heq_of_eq hi).trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm))

/-- 共同左単位の全比較を角へ制限すると、以前の同じ実面単位比較を回収する。 -/
lemma d3DoubleEndpointJointLeftTargetIso_face (k l : Fin 2) :
    HEq (d3DoubleEndpointJointLeftTargetIso.{u}.precomp
      (lift (𝟙 PointedKanInfinity)
        (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l))))
      (d3DoubleEndpointLeftTargetIso k l) := by
  unfold d3DoubleEndpointJointLeftTargetIso
  refine (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorIsoOfEq_precomp_heq _ _ _ _).trans ?_
  refine (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorIso_precomp_precomp_heq _ _ _).trans ?_
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_heq_of_map_eq _ (d3PointedKanSquarePair_corner k l)).trans
    (d3DoubleEndpointLeftTargetParameter_stage k l)

/-- 共同右単位も、全 Hom 上の角制限で以前の同じ指定比較に一致する。 -/
lemma d3DoubleEndpointJointRightTargetIso_face (k l : Fin 2) :
    HEq (d3DoubleEndpointJointRightTargetIso.{u}.precomp
      (lift (𝟙 PointedKanInfinity)
        (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l))))
      (d3DoubleEndpointRightTargetIso k l) := by
  unfold d3DoubleEndpointJointRightTargetIso
  refine (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorIsoOfEq_precomp_heq _ _ _ _).trans ?_
  refine (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorIso_precomp_precomp_heq _ _ _).trans ?_
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_heq_of_map_eq _ (d3PointedKanSquarePair_corner k l)).trans
    (d3DoubleEndpointRightTargetParameter_stage k l)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
