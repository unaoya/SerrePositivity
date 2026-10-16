module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionRightUnit

/-! # 全導来bimodule合成の左単位と解像度に関する自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

def derivedBimoduleLeftUnitFunctor (hC : localHomKFlat A C) :
    DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B C :=
  derivedBimoduleComposeFunctor A B B C hC ⋙
    (CategoryTheory.evaluation (DerivedBimoduleCategory A B B) (DerivedBimoduleCategory A B C)).obj
      ((bimoduleToDerived A B B).obj (rightKFlatDiagonal A B).obj)

def derivedBimoduleLeftUnitResolutionIso (hC : localHomKFlat A C) (Q : BimoduleCategory A B C)
    (R : RightKFlatBimoduleCategory A B C) (q : R.obj ⟶ Q)
    (hq : BimoduleCategory.quasiIso A B C q) :
    (derivedBimoduleLeftUnitFunctor A B C hC).obj ((bimoduleToDerived A B C).obj Q) ≅
      (bimoduleToDerived A B C).obj Q :=
  (derivedBimoduleComposeResolutionComputation A B B C hC Q R q hq).app
      ((bimoduleToDerived A B B).obj (rightKFlatDiagonal A B).obj) ≪≫
    (bimoduleToDerived A B C).mapIso
      (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C R.obj)) ≪≫
    bimoduleDerivedIso A B C q hq

lemma derivedBimoduleLeftUnitResolutionIso_naturality (hC : localHomKFlat A C)
    {Q Q' : BimoduleCategory A B C} (R S : RightKFlatBimoduleCategory A B C)
    (q : R.obj ⟶ Q) (r : S.obj ⟶ Q')
    (hq : BimoduleCategory.quasiIso A B C q) (hr : BimoduleCategory.quasiIso A B C r)
    (f : Q ⟶ Q') (g : R ⟶ S)
    (h : (bimoduleToDerived A B C).map q ≫ (bimoduleToDerived A B C).map f =
      (bimoduleToDerived A B C).map g.hom ≫ (bimoduleToDerived A B C).map r) :
    (derivedBimoduleLeftUnitFunctor A B C hC).map ((bimoduleToDerived A B C).map f) ≫
        (derivedBimoduleLeftUnitResolutionIso A B C hC Q' S r hr).hom =
      (derivedBimoduleLeftUnitResolutionIso A B C hC Q R q hq).hom ≫
        (bimoduleToDerived A B C).map f := by
  let Δ := (bimoduleToDerived A B B).obj (rightKFlatDiagonal A B).obj
  let k := (derivedComposeWithMap A B B C R.property S.property g.hom).app Δ
  let c := (bimoduleToDerived A B C).map
    (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C S.obj)).hom
  let d := (bimoduleToDerived A B C).map r
  have hc := NatTrans.congr_app
    (derivedBimoduleComposeResolutionComputation_naturality A B B C hC R S q r hq hr f g h) Δ
  simp only [NatTrans.comp_app] at hc
  have hu : k ≫ c = (bimoduleToDerived A B C).map
      (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C R.obj)).hom ≫
        (bimoduleToDerived A B C).map g.hom := by
    change (derivedComposeWithMap A B B C R.property S.property g.hom).app
      ((bimoduleToDerived A B B).obj (rightKFlatDiagonal A B).obj) ≫ _ = _
    rw [derivedComposeWithMap_base_app, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp]
    exact congrArg (bimoduleToDerived A B C).map (leftBimoduleUnitIso_naturality A B C g.hom)
  change ((derivedBimoduleComposeFunctor A B B C hC).map
      ((bimoduleToDerived A B C).map f)).app Δ ≫
      ((derivedBimoduleComposeResolutionComputation A B B C hC Q' S r hr).hom.app Δ ≫
        (c ≫ d)) =
    ((derivedBimoduleComposeResolutionComputation A B B C hC Q R q hq).hom.app Δ ≫
      ((bimoduleToDerived A B C).map
        (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C R.obj)).hom ≫
          (bimoduleToDerived A B C).map q)) ≫ (bimoduleToDerived A B C).map f
  simp only [← Category.assoc]
  rw [hc]
  simp only [Category.assoc]
  rw [← Category.assoc k c d, hu]
  simp only [Category.assoc]
  rw [← h]

def derivedBimoduleLeftUnitBaseIso (hC : localHomKFlat A C) (Q : BimoduleCategory A B C) :
    (derivedBimoduleLeftUnitFunctor A B C hC).obj ((bimoduleToDerived A B C).obj Q) ≅
      (bimoduleToDerived A B C).obj Q :=
  derivedBimoduleLeftUnitResolutionIso A B C hC Q (rightKFlatResolutionObj A B C hC Q)
    (bimoduleCanonicalSemifreeResolution A B C Q).π
    (bimoduleCanonicalSemifreeResolution A B C Q).quasiIso

lemma derivedBimoduleLeftUnitBaseIso_naturality (hC : localHomKFlat A C)
    {Q Q' : BimoduleCategory A B C} (f : Q ⟶ Q') :
    (derivedBimoduleLeftUnitFunctor A B C hC).map ((bimoduleToDerived A B C).map f) ≫
        (derivedBimoduleLeftUnitBaseIso A B C hC Q').hom =
      (derivedBimoduleLeftUnitBaseIso A B C hC Q).hom ≫ (bimoduleToDerived A B C).map f := by
  apply derivedBimoduleLeftUnitResolutionIso_naturality A B C hC
    (rightKFlatResolutionObj A B C hC Q) (rightKFlatResolutionObj A B C hC Q')
    _ _ _ _ f (rightKFlatReplacementMap A B C hC f)
  have h := rightKFlatGlobalAugmentation_naturality A B C hC f
  change (rightKFlatDerivedInclusion A B C).map
      ((rightKFlatToDerived A B C).map (rightKFlatReplacementMap A B C hC f)) ≫ _ = _ at h
  rw [rightKFlatDerivedInclusion_map_base] at h
  exact h.symm

def derivedBimoduleLeftUnitLocalizedIso (hC : localHomKFlat A C) :
    bimoduleToDerived A B C ⋙ derivedBimoduleLeftUnitFunctor A B C hC ≅ bimoduleToDerived A B C :=
  NatIso.ofComponents (derivedBimoduleLeftUnitBaseIso A B C hC)
    (fun f => derivedBimoduleLeftUnitBaseIso_naturality A B C hC f)

def derivedBimoduleLeftUnitIso (hC : localHomKFlat A C) :
    derivedBimoduleLeftUnitFunctor A B C hC ≅ 𝟭 (DerivedBimoduleCategory A B C) :=
  Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (bimoduleToDerived A B C ⋙ derivedBimoduleLeftUnitFunctor A B C hC) (bimoduleToDerived A B C)
    (derivedBimoduleLeftUnitFunctor A B C hC) (𝟭 _) (derivedBimoduleLeftUnitLocalizedIso A B C hC)

end SerrePositivity.DifferentialGraded.BimoduleTensor
