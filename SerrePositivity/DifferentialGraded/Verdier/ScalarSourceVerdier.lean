module
public import SerrePositivity.DifferentialGraded.Verdier.ScalarExtensionTria

/-! # 元の tria 上の係数変更から直接誘導する Verdier 関手

商との局所同値による輸送に先立ち、元の実際の係数変更を局所化する。
-/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全 Perf 上の既存の主導来係数変更。生成集合の型を明示して固定する。 -/
def sourceScalarPerfectFunctor :
    PerfectModuleCategory A D ⥤ PerfectModuleCategory A' (ScalarExtension.DGBaseChange φ D) :=
  perfectScalarDerivedExtension φ D Set.univ

instance sourceScalarPerfectFunctorCommShift : (sourceScalarPerfectFunctor φ D).CommShift ℤ :=
  perfectScalarDerivedExtensionCommShift φ D Set.univ
instance sourceScalarPerfectFunctorIsTriangulated :
    (sourceScalarPerfectFunctor φ D).IsTriangulated :=
  perfectScalarDerivedExtensionIsTriangulated φ D Set.univ

/-- 係数変更した実際の代表加群の導来計算。同じ対象を生成元に取る。 -/
def sourceScalarRepresentableIso (d : D) :
    (ScalarExtension.derivedExtension φ D).obj (triaRepresentable A D d).obj ≅
      (triaRepresentable A' (ScalarExtension.DGBaseChange φ D) d).obj := by
  let M := ForgetEnrichment.of (Complex A) (representable A d)
  let e : (ScalarExtension.moduleExtension φ D).obj M ≅
      ForgetEnrichment.of (Complex A')
        (representable A' (show ScalarExtension.DGBaseChange φ D from d)) :=
    eqToIso (by
      change ForgetEnrichment.of (Complex A')
        (ScalarExtension.rightModule φ D (representable A d)) = _
      rw [scalarRepresentable_eq])
  exact scalarDerivedProjectiveComputation φ D M (representable_homotopicallyProjective A D d) ≪≫
    (moduleToDerived A' (ScalarExtension.DGBaseChange φ D)).mapIso e

lemma sourceScalarTria_mem (X : TriaCategory A D) :
    derivedFiniteCellOver A' (ScalarExtension.DGBaseChange φ D) Set.univ
      ((ScalarExtension.derivedExtension φ D).obj X.obj) :=
  exactPerfectFunctor_tria A D (ScalarExtension.DGBaseChange φ D)
    (sourceScalarPerfectFunctor φ D)
    (fun d => (derivedFiniteCellOver A' (ScalarExtension.DGBaseChange φ D) Set.univ).prop_of_iso
      (sourceScalarRepresentableIso φ D d).symm
      (triaRepresentable A' (ScalarExtension.DGBaseChange φ D) d).property) X

/-- 元の dg 圏の実際の導来係数変更を tria に制限する。 -/
def sourceScalarTriaFunctor :
    TriaCategory A D ⥤ TriaCategory A' (ScalarExtension.DGBaseChange φ D) :=
  (derivedFiniteCellOver A' _ Set.univ).lift
    (triaToPerfect A D ⋙ sourceScalarPerfectFunctor φ D ⋙ (modulePerfect A' _).ι)
    (sourceScalarTria_mem φ D)

instance sourceScalarTriaFunctorCommShift : (sourceScalarTriaFunctor φ D).CommShift ℤ := by
  dsimp [sourceScalarTriaFunctor]
  infer_instance
instance sourceScalarTriaFunctorIsTriangulated : (sourceScalarTriaFunctor φ D).IsTriangulated := by
  dsimp [sourceScalarTriaFunctor]
  infer_instance

/-- 制限を忘れると、元の主導来係数変更そのものに戻る。 -/
def sourceScalarTriaInclusionIso :
    sourceScalarTriaFunctor φ D ⋙ triaInclusion A' (ScalarExtension.DGBaseChange φ D) ≅
      triaInclusion A D ⋙ ScalarExtension.derivedExtension φ D := Iso.refl _

variable (S : Set D)

lemma sourceScalarTriaFunctor_image {X : TriaCategory A D} (hX : triaImage A D S X) :
    triaImage A' (ScalarExtension.DGBaseChange φ D) S ((sourceScalarTriaFunctor φ D).obj X) := by
  let P := (triaImage A' (ScalarExtension.DGBaseChange φ D) S).inverseImage
    (sourceScalarTriaFunctor φ D)
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  apply ((triaImage_le_iff_generators A D S P).2 ?_) X hX
  intro d hd
  exact (derivedFiniteCellOver A' (ScalarExtension.DGBaseChange φ D) S).prop_of_iso
    (sourceScalarRepresentableIso φ D d).symm
    (triaImage_representable A' (ScalarExtension.DGBaseChange φ D) S d hd)

lemma sourceScalarTriaFunctor_verdier_inverts :
    (triaImage A D S).trW.IsInvertedBy
      (sourceScalarTriaFunctor φ D ⋙ triaQuotient A' (ScalarExtension.DGBaseChange φ D) S) := by
  intro X Y f hf
  exact (triangulatedKernel_trW_iff _ f).1
    ((triaImage A D S).trW_monotone (fun X hX =>
      verdierQuotient_isZero (triaImage A' (ScalarExtension.DGBaseChange φ D) S) _
        (sourceScalarTriaFunctor_image φ D S hX)) _ hf)

/-- 局所 K-flat 条件を使わず、元の係数変更を先に Verdier 局所化した関手。 -/
def sourceScalarVerdierFunctor :
    TriaQuotient A D S ⥤ TriaQuotient A' (ScalarExtension.DGBaseChange φ D) S :=
  Localization.lift
    (sourceScalarTriaFunctor φ D ⋙ triaQuotient A' (ScalarExtension.DGBaseChange φ D) S)
    (sourceScalarTriaFunctor_verdier_inverts φ D S) (triaQuotient A D S)

def sourceScalarVerdierFactors :
    triaQuotient A D S ⋙ sourceScalarVerdierFunctor φ D S ≅
      sourceScalarTriaFunctor φ D ⋙ triaQuotient A' (ScalarExtension.DGBaseChange φ D) S :=
  Localization.fac _ (sourceScalarTriaFunctor_verdier_inverts φ D S) _

instance sourceScalarVerdierLifting :
    Localization.Lifting (triaQuotient A D S) (triaImage A D S).trW
      (sourceScalarTriaFunctor φ D ⋙ triaQuotient A' (ScalarExtension.DGBaseChange φ D) S)
      (sourceScalarVerdierFunctor φ D S) :=
  Localization.liftingLift _ (sourceScalarTriaFunctor_verdier_inverts φ D S) _

instance sourceScalarVerdierFunctorCommShift : (sourceScalarVerdierFunctor φ D S).CommShift ℤ :=
  Functor.commShiftOfLocalization (triaQuotient A D S) (triaImage A D S).trW ℤ
    (sourceScalarTriaFunctor φ D ⋙ triaQuotient A' (ScalarExtension.DGBaseChange φ D) S)
    (sourceScalarVerdierFunctor φ D S)
instance sourceScalarVerdierFactorsCommShift :
    NatTrans.CommShift (sourceScalarVerdierFactors φ D S).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization (triaQuotient A D S) (triaImage A D S).trW ℤ
    (sourceScalarTriaFunctor φ D ⋙ triaQuotient A' (ScalarExtension.DGBaseChange φ D) S)
    (sourceScalarVerdierFunctor φ D S)
instance sourceScalarVerdierFunctorIsTriangulated :
    (sourceScalarVerdierFunctor φ D S).IsTriangulated := by
  have : (triaQuotient A D S).mapArrow.EssSurj :=
    Localization.essSurj_mapArrow (triaQuotient A D S) (triaImage A D S).trW
  exact Functor.isTriangulated_of_precomp_iso (sourceScalarVerdierFactors φ D S)

def sourceScalarVerdierFactorsTriangle := Functor.mapTriangleIso (sourceScalarVerdierFactors φ D S)
end SerrePositivity.DifferentialGraded
