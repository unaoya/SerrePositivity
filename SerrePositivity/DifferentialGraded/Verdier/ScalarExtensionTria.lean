module
public import SerrePositivity.DifferentialGraded.Verdier.ScalarExtensionSquare

/-! # 未完備の局所商・指定 Verdier 比較と非平坦係数変更

明示的 dg 商上の実際の導来係数変更を tria に制限し、局所商同値に沿って運ぶ。
元の dg 圏の tria 上の係数変更を先に Verdier 局所化する構成との一致は含めない。
-/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- retract を加える前の tria から Perf への実際の包含。 -/
def triaToPerfect : TriaCategory A D ⥤ PerfectModuleCategory A D :=
  (modulePerfect A D).lift (triaInclusion A D)
    (fun X => (derivedFiniteCellOver A D Set.univ).le_retractClosure _ X.property)

instance triaToPerfectCommShift : (triaToPerfect A D).CommShift ℤ := by
  dsimp [triaToPerfect]
  infer_instance

instance triaToPerfectIsTriangulated : (triaToPerfect A D).IsTriangulated := by
  dsimp [triaToPerfect]
  infer_instance

section General
variable {A' : Type u} [CommRing A'] (E : Type w) [DGCategory A' E] [Small.{u} E]
  (T : PerfectModuleCategory A D ⥤ PerfectModuleCategory A' E)
  [T.CommShift ℤ] [T.IsTriangulated]

/-- 代表加群を tria に送る完全関手は、tria 全体を tria に送る。 -/
lemma exactPerfectFunctor_tria
    (hgen : ∀ d : D, derivedFiniteCellOver A' E Set.univ
      (T.obj ((triaToPerfect A D).obj (triaRepresentable A D d))).obj)
    (X : TriaCategory A D) :
    derivedFiniteCellOver A' E Set.univ (T.obj ((triaToPerfect A D).obj X)).obj := by
  let P := (derivedFiniteCellOver A' E Set.univ).inverseImage
    (triaToPerfect A D ⋙ T ⋙ (modulePerfect A' E).ι)
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  exact ((triaImage_le_iff_generators A D Set.univ P).2 (fun d _ => hgen d)) X X.property
end General

namespace DGQuotient
variable {A D} {A' : Type u} [CommRing A'] (φ : A →+* A') (S : Set D)

/-- 係数変更と固定 path の dg 比較を合成すると、同じ対象の代表加群になる。 -/
def quotientScalarRepresentableIso (z : QuotientObject D S) :
    ((quotientScalarPerfectFunctor φ D S).obj
      ((triaToPerfect A (QuotientObject D S)).obj
        (triaRepresentable A (QuotientObject D S) z))).obj ≅
      (triaRepresentable A' (QuotientObject (ScalarExtension.DGBaseChange φ D) S)
        ⟨z.val⟩).obj := by
  let Q := QuotientObject D S
  let Q' := QuotientObject (ScalarExtension.DGBaseChange φ D) S
  let M := ForgetEnrichment.of (Complex A) (representable A z)
  let e : (ScalarExtension.moduleExtension φ Q).obj M ≅
      ForgetEnrichment.of (Complex A')
        (representable A' (show ScalarExtension.DGBaseChange φ Q from z)) :=
    eqToIso (by
      change ForgetEnrichment.of (Complex A')
        (ScalarExtension.rightModule φ Q (representable A z)) = _
      rw [scalarRepresentable_eq])
  exact (dgDerivedExtension A' (ScalarExtension.DGBaseChange φ Q) Q'
    (quotientBaseChangeDGFunctor φ D S)).mapIso
      (scalarDerivedProjectiveComputation φ Q M (representable_homotopicallyProjective A Q z) ≪≫
        (moduleToDerived A' (ScalarExtension.DGBaseChange φ Q)).mapIso e) ≪≫
    dgDerivedExtensionRepresentableIso A' (ScalarExtension.DGBaseChange φ Q) Q'
      (quotientBaseChangeDGFunctor φ D S) z

lemma quotientScalarPerfect_tria (X : TriaCategory A (QuotientObject D S)) :
    derivedFiniteCellOver A' (QuotientObject (ScalarExtension.DGBaseChange φ D) S) Set.univ
      ((quotientScalarPerfectFunctor φ D S).obj
        ((triaToPerfect A (QuotientObject D S)).obj X)).obj :=
  exactPerfectFunctor_tria A (QuotientObject D S) _ (quotientScalarPerfectFunctor φ D S)
    (fun z => (derivedFiniteCellOver A' _ Set.univ).prop_of_iso
      (quotientScalarRepresentableIso φ S z).symm
      (triaRepresentable A' (QuotientObject (ScalarExtension.DGBaseChange φ D) S)
        ⟨z.val⟩).property) X

/-- 明示的 dg 商の tria 上での、実際の導来係数変更の制限。 -/
def quotientScalarTriaFunctor : TriaCategory A (QuotientObject D S) ⥤
    TriaCategory A' (QuotientObject (ScalarExtension.DGBaseChange φ D) S) :=
  (derivedFiniteCellOver A' _ Set.univ).lift
    (triaToPerfect A (QuotientObject D S) ⋙ quotientScalarPerfectFunctor φ D S ⋙
      (modulePerfect A' _).ι) (quotientScalarPerfect_tria φ S)

instance quotientScalarTriaFunctorCommShift : (quotientScalarTriaFunctor φ S).CommShift ℤ := by
  dsimp [quotientScalarTriaFunctor]
  infer_instance

instance quotientScalarTriaFunctorIsTriangulated :
    (quotientScalarTriaFunctor φ S).IsTriangulated := by
  dsimp [quotientScalarTriaFunctor]
  infer_instance

/-- tria への制限は、retract を加える Perf への包含と可換する。 -/
def quotientScalarTriaPerfectSquare :
    quotientScalarTriaFunctor φ S ⋙
        triaToPerfect A' (QuotientObject (ScalarExtension.DGBaseChange φ D) S) ≅
      triaToPerfect A (QuotientObject D S) ⋙ quotientScalarPerfectFunctor φ D S :=
  Iso.refl _

/-- tria の比較の全辺を忘れると U12f・U15d の実際の導来関手となる。 -/
def quotientScalarTriaInclusionIso :
    quotientScalarTriaFunctor φ S ⋙
        triaInclusion A' (QuotientObject (ScalarExtension.DGBaseChange φ D) S) ≅
      triaInclusion A (QuotientObject D S) ⋙
        ScalarExtension.derivedExtension φ (QuotientObject D S) ⋙
          dgDerivedExtension A' (ScalarExtension.DGBaseChange φ (QuotientObject D S))
            (QuotientObject (ScalarExtension.DGBaseChange φ D) S)
            (quotientBaseChangeDGFunctor φ D S) := Iso.refl _

variable (h : localKFlat A D S) (h' : localKFlat A' (ScalarExtension.DGBaseChange φ D) S)

/-- 未完備の指定 Verdier 商上へ、局所比較に沿って運んだ係数変更。 -/
def localScalarTriaExtension : TriaQuotient A D S ⥤
    TriaQuotient A' (ScalarExtension.DGBaseChange φ D) S :=
  (localQuotientTriaEquivalence A D S h).functor ⋙ quotientScalarTriaFunctor φ S ⋙
    (localQuotientTriaEquivalence A' (ScalarExtension.DGBaseChange φ D) S h').inverse

instance localScalarTriaExtensionCommShift : (localScalarTriaExtension φ S h h').CommShift ℤ := by
  dsimp [localScalarTriaExtension]
  infer_instance

instance localScalarTriaExtensionIsTriangulated :
    (localScalarTriaExtension φ S h h').IsTriangulated := by
  dsimp [localScalarTriaExtension]
  infer_instance

def localScalarTriaSquare :
    localScalarTriaExtension φ S h h' ⋙
        (localQuotientTriaEquivalence A' (ScalarExtension.DGBaseChange φ D) S h').functor ≅
      (localQuotientTriaEquivalence A D S h).functor ⋙ quotientScalarTriaFunctor φ S :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (localQuotientTriaEquivalence A'
        (ScalarExtension.DGBaseChange φ D) S h').counitIso ≪≫ Functor.rightUnitor _)

instance localScalarTriaSquareCommShift :
    NatTrans.CommShift (localScalarTriaSquare φ S h h').hom ℤ := by
  dsimp only [localScalarTriaSquare, Iso.trans_hom, isoWhiskerLeft_hom]
  infer_instance

/-- 既存の指定 `quotientVerdierComparison` そのものに対する係数変更正方形。 -/
def canonicalScalarTriaSquare :
    localScalarTriaExtension φ S h h' ⋙
        quotientVerdierComparison A' (ScalarExtension.DGBaseChange φ D) S ≅
      quotientVerdierComparison A D S ⋙ quotientScalarTriaFunctor φ S :=
  isoWhiskerLeft _ (quotientComparisonModelsIso A' (ScalarExtension.DGBaseChange φ D) S).symm ≪≫
    localScalarTriaSquare φ S h h' ≪≫
      isoWhiskerRight (quotientComparisonModelsIso A D S) _

def localScalarTriaSquareTriangle := Functor.mapTriangleIso (localScalarTriaSquare φ S h h')
end DGQuotient
end SerrePositivity.DifferentialGraded
