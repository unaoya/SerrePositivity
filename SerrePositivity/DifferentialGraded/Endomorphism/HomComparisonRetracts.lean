module
public import SerrePositivity.DifferentialGraded.Endomorphism.HomMapNaturality
public import SerrePositivity.DifferentialGraded.Module.Precomposition

/-! # 再構成Homの擬同型条件はK内の始域retractに安定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

lemma endomorphismHomComparison_of_homotopyRetract
    {P Q : ModuleCategory A D} (i : P ⟶ Q) (r : Q ⟶ P)
    (h : (moduleToHomotopy A D).map (i ≫ r) = (moduleToHomotopy A D).map (𝟙 P))
    (T : ModuleCategory A D)
    (hQ : QuasiIso ((endomorphismModuleHom A D E).map Q T)) :
    QuasiIso ((endomorphismModuleHom A D E).map P T) := by
  let F := endomorphismModuleHom A D E
  obtain ⟨hh⟩ := (moduleToHomotopy_map_eq_iff A D (i ≫ r) (𝟙 P)).mp h
  have hF : (moduleToHomotopy A (EndomorphismObject E)).map (F.onClosed.map (i ≫ r)) =
      (moduleToHomotopy A (EndomorphismObject E)).map (F.onClosed.map (𝟙 P)) :=
    congrArg F.onHomotopy.map h
  obtain ⟨ht⟩ := (moduleToHomotopy_map_eq_iff A (EndomorphismObject E) _ _).mp hF
  constructor
  intro q
  apply (quasiIsoAt_iff_isIso_homologyMap _ q).2
  have hs := (moduleHomPrecomposeHomotopy A D hh T).homologyMap_eq q
  simp only [eHomWhiskerRight_comp, eHomWhiskerRight_id, homologyMap_comp, homologyMap_id] at hs
  have ht' := (moduleHomPrecomposeHomotopy A (EndomorphismObject E) ht
    (F.onClosed.obj T)).homologyMap_eq q
  simp only [Functor.map_comp, eHomWhiskerRight_comp, homologyMap_comp] at ht'
  have htId := congrArg (fun k => homologyMap
    (eHomWhiskerRight (Complex A) k (F.onClosed.obj T)) q) (F.onClosed.map_id P)
  simp only [eHomWhiskerRight_id, homologyMap_id] at htId
  have htFinal := ht'.trans htId
  let a : RetractArrow (homologyMap (F.map P T) q) (homologyMap (F.map Q T) q) :=
    { i := Arrow.homMk
        (homologyMap (eHomWhiskerRight (Complex A) r T) q)
        (homologyMap (eHomWhiskerRight (Complex A) (F.onClosed.map r) (F.onClosed.obj T)) q)
        (by
          have hn := congrArg (fun k => homologyMap k q) (dgHomMap_precompose F r T)
          simp only [homologyMap_comp] at hn
          exact hn)
      r := Arrow.homMk
        (homologyMap (eHomWhiskerRight (Complex A) i T) q)
        (homologyMap (eHomWhiskerRight (Complex A) (F.onClosed.map i) (F.onClosed.obj T)) q)
        (by
          have hn := congrArg (fun k => homologyMap k q) (dgHomMap_precompose F i T)
          simp only [homologyMap_comp] at hn
          exact hn)
      retract := by
        apply Arrow.hom_ext
        · exact hs
        · exact htFinal }
  have : QuasiIso (F.map Q T) := hQ
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms (ModuleCat A)) a
    (by infer_instance)

lemma endomorphismHomComparison_of_retract
    {P Q : ModuleCategory A D}
    (a : Retract ((moduleToHomotopy A D).obj P) ((moduleToHomotopy A D).obj Q))
    (T : ModuleCategory A D)
    (hQ : QuasiIso ((endomorphismModuleHom A D E).map Q T)) :
    QuasiIso ((endomorphismModuleHom A D E).map P T) := by
  obtain ⟨i, hi⟩ := (moduleToHomotopy A D).map_surjective a.i
  obtain ⟨r, hr⟩ := (moduleToHomotopy A D).map_surjective a.r
  apply endomorphismHomComparison_of_homotopyRetract A D E i r _ T hQ
  rw [CategoryTheory.Functor.map_comp, hi, hr, a.retract]
  exact ((moduleToHomotopy A D).map_id P).symm

/-- 全ての終域に対し再構成Hom写像が擬同型になる、K(D)内の始域の性質。 -/
def endomorphismHomComparisonLocus : ObjectProperty (ModuleHomotopyCategory A D) :=
  fun X => ∀ T : ModuleCategory A D, QuasiIso ((endomorphismModuleHom A D E).map X.as T)

instance endomorphismHomComparisonLocusStableUnderRetracts :
    (endomorphismHomComparisonLocus A D E).IsStableUnderRetracts where
  of_retract a hQ T := endomorphismHomComparison_of_retract A D E a T (hQ T)

lemma endomorphismHomComparisonLocus_generator :
    endomorphismHomComparisonLocus A D E
      ((moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) E)) := by
  intro T
  exact endomorphismModuleHom_generator_quasiIso A D E T

end SerrePositivity.DifferentialGraded
