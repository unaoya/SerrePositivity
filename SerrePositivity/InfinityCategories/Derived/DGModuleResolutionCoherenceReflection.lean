module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionLocalization
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerAlgebra
/-!
概要：指定半自由分解による前合成は、全関手の変換と同型の等式を反映する。
方針：局所化の全写像空間充満忠実性を h Fun へ移し、指定前合成と照合する。
規約：頂点ごとの等式から結論しない。使われ方：一般 kernel の coherence の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalClosed
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
/-- 指定半自由分解に沿う前合成は、全関手 ∞ 圏の全写像空間上で充満忠実。 -/
lemma dgModuleResolution_precomposition_isFullyFaithful
    (Y : SSet.{max (u + 1) v}) [Quasicategory Y] :
    IsFullyFaithful ((pre (dgModuleResolvedInfinity R (RightModule R E) E
      (DGFunctor.id (RightModule R E)))).app Y) :=
  (dgModuleResolution_isLocalization R E).precomposition_isFullyFaithful Y
/-- 同じ全関手変換の等式は、指定半自由分解に沿う前合成後の等式から反映される。 -/
lemma dgModuleResolution_precompositionHom_injective
    (Y : SSet.{max (u + 1) v}) [Quasicategory Y]
    (F G : dgModuleDerivedInfinityCategory R E ⟶ Y) :
    Function.Injective
      ((hoFunctor.map ((pre (dgModuleResolvedInfinity R (RightModule R E) E
        (DGFunctor.id (RightModule R E)))).app Y)).toFunctor.map :
      FunctorHom F G → FunctorHom
        (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)) ≫ F)
        (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)) ≫ G)) :=
  (dgModuleResolution_precomposition_isFullyFaithful R E Y).toHoFullyFaithful.homEquiv.injective
/-- 同じ指定全関手同型の等式も、指定分解による前合成後に検査できる。 -/
lemma dgModuleResolution_precompositionIso_injective
    (Y : SSet.{max (u + 1) v}) [Quasicategory Y]
    (F G : dgModuleDerivedInfinityCategory R E ⟶ Y)
    (e f : FunctorIso F G)
    (h : e.precomp (dgModuleResolvedInfinity R (RightModule R E) E
        (DGFunctor.id (RightModule R E))) =
      f.precomp (dgModuleResolvedInfinity R (RightModule R E) E
        (DGFunctor.id (RightModule R E)))) : e = f := by
  apply Iso.ext
  apply dgModuleResolution_precompositionHom_injective R E Y F G
  have hh := congrArg Iso.hom h
  simpa only [F2.functorIso_precomp_eq_mapIso, Functor.mapIso_hom] using! hh
end SerrePositivity.InfinityCategories
