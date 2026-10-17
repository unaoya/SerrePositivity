module
public import SerrePositivity.DifferentialGraded.Endomorphism.EnhancementHomotopyAdjunction
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectAdjunction

/-! # 実際のenhancement tensorと主Perf tensorの自然比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)

/-- 既存のHom比較をU13同値の逆で運んだ、二つの実際の右随伴の比較。 -/
def perfectEndomorphismEnhancementRightComparison :
    (perfectDGModuleHomotopyEquivalence A D S).inverse ⋙
        (perfectEndomorphismDG A D S E hgen).onHomotopy ≅
      perfectEndomorphismHomToPerfect A D S E hgen ⋙
        (perfectDGModuleHomotopyEquivalence A (EndomorphismObject E.val) Set.univ).inverse := by
  let P := perfectDGModuleHomotopyEquivalence A D S
  let Q := perfectDGModuleHomotopyEquivalence A (EndomorphismObject E.val) Set.univ
  apply Functor.fullyFaithfulCancelRight Q.functor
  exact
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft P.inverse (perfectEndomorphismDerivedComparison A D S E hgen) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight P.counitIso (perfectEndomorphismHomToPerfect A D S E hgen) ≪≫
      Functor.leftUnitor _) ≪≫
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (perfectEndomorphismHomToPerfect A D S E hgen) Q.counitIso ≪≫
      Functor.rightUnitor _).symm

/-- 実際のenhancement随伴をU13同値で運び、既存のHom比較で右随伴を揃える。 -/
def perfectEndomorphismEnhancementTransportedAdjunction :
    (perfectEndomorphismTensorDG A D S E).onHomotopy ⋙
        perfectDGModuleToPerfect A D S ⊣
      perfectEndomorphismHomToPerfect A D S E hgen ⋙
        (perfectDGModuleHomotopyEquivalence A (EndomorphismObject E.val) Set.univ).inverse :=
  ((perfectEndomorphismEnhancementHomotopyAdjunction A D S E hgen).comp
    (perfectDGModuleHomotopyEquivalence A D S).toAdjunction).ofNatIsoRight
      (perfectEndomorphismEnhancementRightComparison A D S E hgen)

/-- 実際のtensorのH⁰と主Perfのtensorの正方形。随伴の一意性で構成する。 -/
def perfectEndomorphismEnhancementTensorComparison :
    (perfectEndomorphismTensorDG A D S E).onHomotopy ⋙
        perfectDGModuleToPerfect A D S ≅
      perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ ⋙
        perfectEndomorphismTensorToPerfect A D S E := by
  exact (perfectEndomorphismEnhancementTransportedAdjunction A D S E hgen).leftAdjointUniq
    ((perfectDGModuleHomotopyEquivalence A (EndomorphismObject E.val) Set.univ).toAdjunction.comp
      (perfectEndomorphismAdjunction A D S E hgen))

lemma perfectEndomorphismEnhancementTensorComparison_unit :
    (perfectEndomorphismEnhancementTransportedAdjunction A D S E hgen).unit ≫
      Functor.whiskerRight (perfectEndomorphismEnhancementTensorComparison A D S E hgen).hom
        (perfectEndomorphismHomToPerfect A D S E hgen ⋙
          (perfectDGModuleHomotopyEquivalence A (EndomorphismObject E.val) Set.univ).inverse) =
    ((perfectDGModuleHomotopyEquivalence A (EndomorphismObject E.val) Set.univ).toAdjunction.comp
      (perfectEndomorphismAdjunction A D S E hgen)).unit :=
  Adjunction.unit_leftAdjointUniq_hom _ _

lemma perfectEndomorphismEnhancementTensorComparison_counit :
    Functor.whiskerLeft
        (perfectEndomorphismHomToPerfect A D S E hgen ⋙
          (perfectDGModuleHomotopyEquivalence A (EndomorphismObject E.val) Set.univ).inverse)
        (perfectEndomorphismEnhancementTensorComparison A D S E hgen).hom ≫
      ((perfectDGModuleHomotopyEquivalence A (EndomorphismObject E.val) Set.univ).toAdjunction.comp
        (perfectEndomorphismAdjunction A D S E hgen)).counit =
    (perfectEndomorphismEnhancementTransportedAdjunction A D S E hgen).counit :=
  Adjunction.leftAdjointUniq_hom_counit _ _

end SerrePositivity.DifferentialGraded
