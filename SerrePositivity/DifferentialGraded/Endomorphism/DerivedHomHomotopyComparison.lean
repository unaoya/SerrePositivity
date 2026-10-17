module
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectDGComparison

/-! # 主Kの再構成Homと主導来Homの全射自然な比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)
variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

/-- dg HomをKへ送って局所化する経路と、局所化して導来Homを取る経路の自然同型。 -/
def endomorphismDerivedHomHomotopyIso :
    (endomorphismModuleHom A D E).onHomotopy ⋙
        moduleHomotopyToDerivedClosed A (EndomorphismObject E) ≅
      moduleHomotopyToDerivedClosed A D ⋙ endomorphismDerivedHom A D E hE :=
  Quotient.natIsoLift (boundaryRelation A (RightModule A D))
    ((Functor.associator (moduleToHomotopy A D) (endomorphismModuleHom A D E).onHomotopy
        (moduleHomotopyToDerivedClosed A (EndomorphismObject E))).symm ≪≫
      Functor.isoWhiskerRight (eqToIso (endomorphismModuleHom A D E).onHomotopy_fac)
        (moduleHomotopyToDerivedClosed A (EndomorphismObject E)) ≪≫
      Functor.associator (endomorphismModuleHom A D E).onClosed
        (moduleToHomotopy A (EndomorphismObject E))
        (moduleHomotopyToDerivedClosed A (EndomorphismObject E)) ≪≫
      Functor.isoWhiskerLeft (endomorphismModuleHom A D E).onClosed
        (moduleToHomotopyDerivedIso A (EndomorphismObject E)) ≪≫
      (eqToIso (endomorphismDerivedHom_fac A D E hE)).symm ≪≫
      Functor.isoWhiskerRight (moduleToHomotopyDerivedIso A D).symm
        (endomorphismDerivedHom A D E hE) ≪≫
      Functor.associator (moduleToHomotopy A D) (moduleHomotopyToDerivedClosed A D)
        (endomorphismDerivedHom A D E hE))

variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)

lemma perfectEndomorphismDG_homotopy_inclusion_square :
    (perfectEndomorphismDG A D S E hgen).onHomotopy ⋙
        (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onHomotopy =
      (perfectDGModuleInclusion A D S).onHomotopy ⋙
        (endomorphismModuleHom A D E.val).onHomotopy := by
  rw [← DGFunctor.onHomotopy_comp, ← DGFunctor.onHomotopy_comp]
  exact congrArg DGFunctor.onHomotopy (perfectEndomorphismDG_inclusion_square A D S E hgen)

/-- U13のenhancement比較と主導来HomのPerf制限の、導来圏内での自然な正方形。 -/
def perfectEndomorphismDerivedComparisonUnderlying :
    ((perfectEndomorphismDG A D S E hgen).onHomotopy ⋙
        perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ) ⋙
          perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ≅
      (perfectDGModuleToPerfect A D S ⋙ perfectEndomorphismHomToPerfect A D S E hgen) ⋙
        perfectModuleInclusion A (EndomorphismObject E.val) Set.univ :=
  Functor.isoWhiskerRight
      (eqToIso (perfectEndomorphismDG_homotopy_inclusion_square A D S E hgen))
      (moduleHomotopyToDerivedClosed A (EndomorphismObject E.val)) ≪≫
    Functor.associator (perfectDGModuleInclusion A D S).onHomotopy
      (endomorphismModuleHom A D E.val).onHomotopy
      (moduleHomotopyToDerivedClosed A (EndomorphismObject E.val)) ≪≫
    Functor.isoWhiskerLeft (perfectDGModuleInclusion A D S).onHomotopy
      (endomorphismDerivedHomHomotopyIso A D E.val E.property.1) ≪≫
    (Functor.associator (perfectDGModuleInclusion A D S).onHomotopy
      (moduleHomotopyToDerivedClosed A D) (endomorphismDerivedHom A D E.val E.property.1)).symm

/-- 充満部分圏への包含の完全忠実性により、正方形をPerf自体の自然同型として保持する。 -/
def perfectEndomorphismDerivedComparison :
    (perfectEndomorphismDG A D S E hgen).onHomotopy ⋙
        perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ ≅
      perfectDGModuleToPerfect A D S ⋙ perfectEndomorphismHomToPerfect A D S E hgen := by
  have : (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ).Full := by
    unfold perfectModuleInclusion
    infer_instance
  have : (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ).Faithful := by
    unfold perfectModuleInclusion
    infer_instance
  exact Functor.fullyFaithfulCancelRight
    (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ)
    (perfectEndomorphismDerivedComparisonUnderlying A D S E hgen)

/-- 主Perf上の導来Homを、U13のenhancement同値の逆とdg比較を用いて計算する。 -/
def perfectEndomorphismHomToPerfectViaEnhancement :
    perfectEndomorphismHomToPerfect A D S E hgen ≅
      (perfectDGModuleHomotopyEquivalence A D S).inverse ⋙
        ((perfectEndomorphismDG A D S E hgen).onHomotopy ⋙
          perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ) :=
  (perfectEndomorphismHomToPerfect A D S E hgen).leftUnitor.symm ≪≫
    Functor.isoWhiskerRight (perfectDGModuleHomotopyEquivalence A D S).counitIso.symm
      (perfectEndomorphismHomToPerfect A D S E hgen) ≪≫
    Functor.associator (perfectDGModuleHomotopyEquivalence A D S).inverse
      (perfectDGModuleHomotopyEquivalence A D S).functor
      (perfectEndomorphismHomToPerfect A D S E hgen) ≪≫
    Functor.isoWhiskerLeft (perfectDGModuleHomotopyEquivalence A D S).inverse
      (perfectEndomorphismDerivedComparison A D S E hgen).symm

instance perfectEndomorphismHomToPerfectFull :
    (perfectEndomorphismHomToPerfect A D S E hgen).Full :=
  Functor.Full.of_iso (perfectEndomorphismHomToPerfectViaEnhancement A D S E hgen).symm

instance perfectEndomorphismHomToPerfectFaithful :
    (perfectEndomorphismHomToPerfect A D S E hgen).Faithful :=
  Functor.Faithful.of_iso (perfectEndomorphismHomToPerfectViaEnhancement A D S E hgen).symm

end SerrePositivity.DifferentialGraded
