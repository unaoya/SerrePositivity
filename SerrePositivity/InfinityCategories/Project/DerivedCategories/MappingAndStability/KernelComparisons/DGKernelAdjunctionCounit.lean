module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.QCatAdjunctionCompositeCounit
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.QCatAdjunctionTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedSectionCounit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGUniversalRightAdjunctionCounit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelAdjunction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelCounitCandidate
/-!
概要：元の一般 kernel 随伴の余単位を、元の指定候補そのものへ厳密に同定する。
方針：入力同値の三角式・随伴合成の式・指定端点輸送を同じ全関手上で照合する。
規約：元の実入力切断と比較同型を保持する。使われ方：一般 RHom の随伴整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の一般 kernel 随伴の余単位は、元の同じ指定候補と厳密に一致する。 -/
lemma dgKernelAdjunction_counitHom (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelAdjunction R D E P).counitHom = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCounitCandidate R D E P := by
  let C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P
  let T := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F
  let R' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCandidate R T (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) G
    (fun y => ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionUniversalCounit R D E P y⟩)
  let a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjunction R T (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) G
    (fun y => ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionUniversalCounit R D E P y⟩)
  let b := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence R C E F).toAdjunction
  have ha : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelAdjunction R D E P) (b.comp a) := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelAdjunction
    dsimp only [_root_.id]
    simp only [eq_mpr_eq_cast]
    exact HEq.trans (cast_heq _ _) (HEq.rfl)
  let e := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedProjectionSectionIso R C E F).postcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G)).precomp R'
  have he : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelRightAdjointCompositeIso R D E P) e := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelRightAdjointCompositeIso
    dsimp only [_root_.id]
    simp only [eq_mp_eq_cast, eq_mpr_eq_cast]
    exact HEq.trans (cast_heq _ _)
      (HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _) (HEq.rfl)))
  have hf : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence R C E F).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence, Category.assoc] using!
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_eq_section_replacement R C E F
  apply Arrow.mk_injective
  have h₀ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.QCatAdjunction.counitHom_arrow_of_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelAdjunction R D E P) (b.comp a) hf rfl ha
  have h₁ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorIso_hom_comp_arrow_of_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelRightAdjointCompositeIso R D E P) e
    (by
      change (R' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P = _
      rw [hf]
      simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence, Category.assoc]) he
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCounit R T (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E) G
      (fun y => ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelResolutionUniversalCounit R D E P y⟩))
  apply h₀.trans
  apply Eq.trans _ h₁.symm
  congr 1
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.QCatAdjunction.comp_counitHom]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSectionEquivalence_counitHom,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjunction_counitHom]
  change _ = e.hom ≫ _
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
