module
public import SerrePositivity.DifferentialGraded.Perfect.RingRetract
public import SerrePositivity.DifferentialGraded.Perfect.KaroubiEquivalence

/-! # 既存PerfectHomotopyのKaroubi包絡と主Perfの比較

元のPerfectHomotopyの冪等完備性を仮定せず、形式的retractを主Perfで実現する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Idempotents
variable (A : Type u) [CommRing A]

/-- 既存有限射影比較の、両辺のKaroubi包絡への実際の延長。 -/
def ringPerfectKaroubiFunctor : Karoubi (PerfectHomotopy A) ⥤
    Karoubi (PerfectModuleCategory A PUnit.{1}) :=
  (functorExtension₂ _ _).obj (perfectHomotopyToDGPerfect A)

instance ringPerfectKaroubiFunctorFull : (ringPerfectKaroubiFunctor A).Full := by
  dsimp [ringPerfectKaroubiFunctor]
  infer_instance

instance ringPerfectKaroubiFunctorFaithful : (ringPerfectKaroubiFunctor A).Faithful := by
  dsimp [ringPerfectKaroubiFunctor]
  infer_instance

instance ringPerfectKaroubiFunctorEssSurj : (ringPerfectKaroubiFunctor A).EssSurj where
  mem_essImage X := by
    obtain ⟨P, ⟨r⟩⟩ := perfectModule_ring_retract_of_perfectHomotopy A X.X
    exact karoubiExtension_mem_essImage (perfectHomotopyToDGPerfect A) X P
      ((karoubiRetract X).trans (r.map (toKaroubi (PerfectModuleCategory A PUnit.{1}))))

instance ringPerfectKaroubiFunctorIsEquivalence : (ringPerfectKaroubiFunctor A).IsEquivalence where

instance ringPerfectKaroubiFunctorAdditive : (ringPerfectKaroubiFunctor A).Additive := by
  dsimp [ringPerfectKaroubiFunctor]
  infer_instance

instance ringPerfectKaroubiFunctorLinear : (ringPerfectKaroubiFunctor A).Linear A := by
  dsimp [ringPerfectKaroubiFunctor]
  infer_instance

instance ringPerfectKaroubiFunctorCommShift : (ringPerfectKaroubiFunctor A).CommShift ℤ := by
  dsimp [ringPerfectKaroubiFunctor]
  infer_instance

instance ringPerfectKaroubiFunctorIsTriangulated :
    (ringPerfectKaroubiFunctor A).IsTriangulated := by
  dsimp [ringPerfectKaroubiFunctor]
  infer_instance

/-- 主Perfの既存冪等完備性を使い、形式的retractを実際のperfect対象として実現する。 -/
def ringPerfectKaroubiRealization :
    Karoubi (PerfectHomotopy A) ⥤ PerfectModuleCategory A PUnit.{1} :=
  (functorExtension _ _).obj (perfectHomotopyToDGPerfect A)

instance ringPerfectKaroubiRealizationIsEquivalence :
    (ringPerfectKaroubiRealization A).IsEquivalence := by
  change (ringPerfectKaroubiFunctor A ⋙
    (toKaroubiEquivalence (PerfectModuleCategory A PUnit.{1})).inverse).IsEquivalence
  infer_instance

instance ringPerfectKaroubiRealizationAdditive : (ringPerfectKaroubiRealization A).Additive := by
  dsimp [ringPerfectKaroubiRealization]
  infer_instance

instance ringPerfectKaroubiRealizationLinear : (ringPerfectKaroubiRealization A).Linear A := by
  let E := toKaroubiEquivalence (PerfectModuleCategory A PUnit.{1})
  have : E.functor.Linear A := by
    change (toKaroubi (PerfectModuleCategory A PUnit.{1})).Linear A
    infer_instance
  have : E.inverse.Linear A := inferInstance
  change (ringPerfectKaroubiFunctor A ⋙ E.inverse).Linear A
  infer_instance

/-- 実現して再びKaroubiへ入れる経路は、元のKaroubi延長と一致する。 -/
def ringPerfectKaroubiRealizationToKaroubiIso :
    ringPerfectKaroubiRealization A ⋙ toKaroubi (PerfectModuleCategory A PUnit.{1}) ≅
      ringPerfectKaroubiFunctor A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ringPerfectKaroubiFunctor A)
      (toKaroubiEquivalence (PerfectModuleCategory A PUnit.{1})).counitIso ≪≫
    Functor.rightUnitor _

instance ringPerfectKaroubiRealizationCommShift :
    (ringPerfectKaroubiRealization A).CommShift ℤ :=
  Functor.CommShift.ofComp (ringPerfectKaroubiRealizationToKaroubiIso A) ℤ

instance ringPerfectKaroubiRealizationToKaroubiIsoCommShift :
    NatTrans.CommShift (ringPerfectKaroubiRealizationToKaroubiIso A).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (ringPerfectKaroubiRealizationToKaroubiIso A) ℤ

instance ringPerfectKaroubiRealizationIsTriangulated :
    (ringPerfectKaroubiRealization A).IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right (ringPerfectKaroubiRealizationToKaroubiIso A)).2
    inferInstance

/-- 実現は元の有限射影ホモトピー圏上では既存の実際の比較に一致する。 -/
def ringPerfectKaroubiRealization_fac :
    toKaroubi (PerfectHomotopy A) ⋙ ringPerfectKaroubiRealization A ≅
      perfectHomotopyToDGPerfect A :=
  karoubiExtensionToCompleteFactors (perfectHomotopyToDGPerfect A)

/-- 既存有限射影ホモトピー圏のKaroubi包絡と主Perfとの実際の同値。 -/
def ringPerfectKaroubiEquivalence :
    Karoubi (PerfectHomotopy A) ≌ PerfectModuleCategory A PUnit.{1} :=
  (ringPerfectKaroubiRealization A).asEquivalence

instance ringPerfectKaroubiEquivalenceFunctorLinear :
    (ringPerfectKaroubiEquivalence A).functor.Linear A := ringPerfectKaroubiRealizationLinear A

instance ringPerfectKaroubiEquivalenceFunctorAdditive :
    (ringPerfectKaroubiEquivalence A).functor.Additive := ringPerfectKaroubiRealizationAdditive A

instance ringPerfectKaroubiEquivalenceFunctorCommShift :
    (ringPerfectKaroubiEquivalence A).functor.CommShift ℤ :=
  ringPerfectKaroubiRealizationCommShift A

instance ringPerfectKaroubiEquivalenceInverseCommShift :
    (ringPerfectKaroubiEquivalence A).inverse.CommShift ℤ :=
  (ringPerfectKaroubiEquivalence A).commShiftInverse ℤ

instance ringPerfectKaroubiEquivalenceCommShift : (ringPerfectKaroubiEquivalence A).CommShift ℤ :=
  (ringPerfectKaroubiEquivalence A).commShift_of_functor ℤ

instance ringPerfectKaroubiEquivalenceIsTriangulated :
    (ringPerfectKaroubiEquivalence A).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (ringPerfectKaroubiRealizationIsTriangulated A)

end SerrePositivity.DifferentialGraded
