module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleHomotopy
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomRetracts
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarYonedaIso
public import SerrePositivity.DifferentialGraded.Module.Precomposition

/-! # 実際のHom係数変更比較のH⁰内始域retract閉性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHom_quasiIso_of_homotopyRetract
    {M N : ModuleCategory A D} (i : M ⟶ N) (r : N ⟶ M)
    (h : (moduleToHomotopy A D).map (i ≫ r) = (moduleToHomotopy A D).map (𝟙 M))
    (P : ModuleCategory A D)
    (hN : QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) P))) :
    QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) P)) := by
  let L := ScalarExtension.extension φ
  let F := ScalarExtension.moduleExtension φ D
  obtain ⟨hh⟩ := (moduleToHomotopy_map_eq_iff A D _ _).mp h
  let ht := scalarModuleHomotopy φ D hh
  constructor
  intro q
  apply (quasiIsoAt_iff_isIso_homologyMap _ q).2
  have hs := ((ModuleCat.extendScalars φ).mapHomotopy
    (moduleHomPrecomposeHomotopy A D hh P)).homologyMap_eq q
  simp only [eHomWhiskerRight_comp, eHomWhiskerRight_id,
    Functor.map_comp, homologyMap_comp] at hs
  have hsId := congrArg (fun k => homologyMap k q)
    (L.map_id (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) P)))
  simp only [homologyMap_id] at hsId
  have ht' := (moduleHomPrecomposeHomotopy A' (ScalarExtension.DGBaseChange φ D)
    ht (F.obj P)).homologyMap_eq q
  simp only [Functor.map_comp, eHomWhiskerRight_comp, homologyMap_comp] at ht'
  have htId := congrArg (fun k => homologyMap
    (eHomWhiskerRight (Complex A') k (F.obj P)) q) (F.map_id M)
  simp only [eHomWhiskerRight_id, homologyMap_id] at htId
  let a : RetractArrow
      (homologyMap (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) P)) q)
      (homologyMap (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N)
        (ForgetEnrichment.to (Complex A) P)) q) :=
    { i := Arrow.homMk
        (homologyMap (L.map (eHomWhiskerRight (Complex A) r P)) q)
        (homologyMap (eHomWhiskerRight (Complex A') (F.map r) (F.obj P)) q)
        (by
          have hn := congrArg (fun k => homologyMap k q) (scalarModuleHom_precompose φ D r P)
          simp only [homologyMap_comp] at hn
          exact hn)
      r := Arrow.homMk
        (homologyMap (L.map (eHomWhiskerRight (Complex A) i P)) q)
        (homologyMap (eHomWhiskerRight (Complex A') (F.map i) (F.obj P)) q)
        (by
          have hn := congrArg (fun k => homologyMap k q) (scalarModuleHom_precompose φ D i P)
          simp only [homologyMap_comp] at hn
          exact hn)
      retract := by
        apply Arrow.hom_ext
        · exact hs.trans hsId
        · exact ht'.trans htId }
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms (ModuleCat A')) a
    (by infer_instance)

lemma scalarModuleHom_quasiIso_of_homotopyCategoryRetract
    {M N : ModuleCategory A D}
    (a : Retract ((moduleToHomotopy A D).obj M) ((moduleToHomotopy A D).obj N))
    (P : ModuleCategory A D)
    (hN : QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) P))) :
    QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) P)) := by
  obtain ⟨i, hi⟩ := (moduleToHomotopy A D).map_surjective a.i
  obtain ⟨r, hr⟩ := (moduleToHomotopy A D).map_surjective a.r
  apply scalarModuleHom_quasiIso_of_homotopyRetract φ D i r _ P hN
  rw [Functor.map_comp, hi, hr, a.retract]
  exact ((moduleToHomotopy A D).map_id M).symm

/-- 任意の終域に対し全次数Hom係数変更比較が擬同型となる始域の性質。 -/
def scalarModuleHomComparisonLocus : ObjectProperty (ModuleHomotopyCategory A D) :=
  fun X => ∀ P : ModuleCategory A D,
    QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) X.as)
      (ForgetEnrichment.to (Complex A) P))

instance scalarModuleHomComparisonLocusStableUnderRetracts :
    (scalarModuleHomComparisonLocus φ D).IsStableUnderRetracts where
  of_retract a hN P := scalarModuleHom_quasiIso_of_homotopyCategoryRetract φ D a P (hN P)

lemma scalarModuleHomComparisonLocus_representable (z : D) :
    scalarModuleHomComparisonLocus φ D
      ((moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) (representable A z))) := by
  intro P
  change QuasiIso (scalarModuleHom φ D (representable A z) (ForgetEnrichment.to (Complex A) P))
  have := scalarModuleHom_representable_isIso φ D z (ForgetEnrichment.to (Complex A) P)
  infer_instance

end SerrePositivity.DifferentialGraded
