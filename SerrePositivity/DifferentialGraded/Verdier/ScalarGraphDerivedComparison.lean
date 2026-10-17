module
public import SerrePositivity.DifferentialGraded.Verdier.ScalarGraphRestriction
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarDerivedProjectiveComparison
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonExtensionCoherence
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations

/-! # 実際の導来係数変更と graph 延長の perfect 始域上の交換

通常の交換同型と射影的モデルでの計算を使い、所望の導来正方形を仮定しない。
-/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

section Computations
variable {C : Type*} [Category* C] (I : C ⥤ ModuleCategory A D)
  (hI : ∀ X, moduleHomotopicallyProjective A D (I.obj X))

/-- 射影的モデルの族に制限した、既存の graph 導来計算の自然同型。 -/
def graphProjectiveFamilyComputation :
    I ⋙ moduleToDerived A D ⋙ dgDerivedExtension A D E F ≅
      I ⋙ (dgModuleExtension A D E F).onClosed ⋙ moduleToDerived A E := by
  let τ := whiskerLeft I (DGQuotient.derivedExtensionUnderivedNatTrans A D E F)
  let : ∀ X, IsIso (τ.app X) := fun X =>
    DGQuotient.derivedExtensionUnderivedMap_isIso A D E F (I.obj X) (hI X)
  let := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- 射影的モデルの族に制限した、既存の係数変更の導来計算の自然同型。 -/
def scalarProjectiveFamilyComputation :
    I ⋙ moduleToDerived A D ⋙ ScalarExtension.derivedExtension φ D ≅
      I ⋙ ScalarExtension.moduleExtension φ D ⋙
        moduleToDerived A' (ScalarExtension.DGBaseChange φ D) := by
  let τ := whiskerLeft I (ScalarExtension.derivedExtensionAugmentation φ D)
  let : ∀ X, IsIso (τ.app X) := fun X =>
    scalarDerivedExtensionAugmentation_isIso_of_projective φ D (I.obj X) (hI X)
  let := NatIso.isIso_of_isIso_app τ
  exact asIso τ
end Computations

/-- 射影的 perfect 代表から全加群への実際の閉零包含。 -/
abbrev scalarGraphPerfectClosedInclusion := (perfectDGModuleInclusion A D Set.univ).onClosed

/-- 閉零射影的 perfect 代表上で、二つの実際の導来複合関手を比較する。 -/
def scalarGraphPerfectClosedSquare :
    scalarGraphPerfectClosedInclusion (A := A) D ⋙ moduleToDerived A D ⋙
        dgDerivedExtension A D E F ⋙ ScalarExtension.derivedExtension φ E ≅
      scalarGraphPerfectClosedInclusion (A := A) D ⋙ moduleToDerived A D ⋙
        ScalarExtension.derivedExtension φ D ⋙
          dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D)
            (ScalarExtension.DGBaseChange φ E)
            (ScalarExtension.dgFunctor φ F) := by
  let I := scalarGraphPerfectClosedInclusion (A := A) D
  have hI : ∀ X, moduleHomotopicallyProjective A D (I.obj X) := fun X =>
    (ForgetEnrichment.to (Complex A) X).property.1
  let J := I ⋙ (dgModuleExtension A D E F).onClosed
  have hJ : ∀ X, moduleHomotopicallyProjective A E (J.obj X) := fun X =>
    dgModuleExtension_homotopicallyProjective A D E F (hI X)
  let I' := I ⋙ ScalarExtension.moduleExtension φ D
  have hI' : ∀ X, moduleHomotopicallyProjective A' (ScalarExtension.DGBaseChange φ D) (I'.obj X) :=
    fun X => scalarModuleExtension_projective_perfect φ D
      (ForgetEnrichment.to (Complex A) X).property.1
      (ForgetEnrichment.to (Complex A) X).property.2
  exact
    isoWhiskerRight (graphProjectiveFamilyComputation (A := A) D E F I hI)
      (ScalarExtension.derivedExtension φ E) ≪≫
    scalarProjectiveFamilyComputation φ E J hJ ≪≫
    isoWhiskerLeft I (isoWhiskerRight (scalarGraphExtensionIso φ D E F)
      (moduleToDerived A' (ScalarExtension.DGBaseChange φ E))) ≪≫
    (graphProjectiveFamilyComputation (A := A') (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.DGBaseChange φ E) (ScalarExtension.dgFunctor φ F) I' hI').symm ≪≫
    isoWhiskerRight (scalarProjectiveFamilyComputation φ D I hI).symm
      (dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D) (ScalarExtension.DGBaseChange φ E)
        (ScalarExtension.dgFunctor φ F))

/-- 閉零代表から H⁰ への商の充満性によって比較を降ろす。 -/
def scalarGraphPerfectHomotopySquare :
    perfectDGModuleToDerived A D Set.univ ⋙
        dgDerivedExtension A D E F ⋙ ScalarExtension.derivedExtension φ E ≅
      perfectDGModuleToDerived A D Set.univ ⋙ ScalarExtension.derivedExtension φ D ⋙
        dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D) (ScalarExtension.DGBaseChange φ E)
          (ScalarExtension.dgFunctor φ F) :=
  Quotient.natIsoLift (boundaryRelation A (PerfectDGModuleOver A D Set.univ))
    ((associator _ _ _).symm ≪≫
      isoWhiskerRight (perfectDGModuleClosedToDerivedIso A D Set.univ)
        (dgDerivedExtension A D E F ⋙ ScalarExtension.derivedExtension φ E) ≪≫
      scalarGraphPerfectClosedSquare φ D E F ≪≫
      isoWhiskerRight (perfectDGModuleClosedToDerivedIso A D Set.univ).symm
        (ScalarExtension.derivedExtension φ D ⋙
          dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D)
            (ScalarExtension.DGBaseChange φ E)
            (ScalarExtension.dgFunctor φ F)) ≪≫ associator _ _ _)

/-- 元の Perf の包含上の、係数変更と graph 延長の実際の導来正方形。 -/
def scalarGraphPerfectDerivedSquare :
    (modulePerfect A D).ι ⋙ dgDerivedExtension A D E F ⋙ ScalarExtension.derivedExtension φ E ≅
      (modulePerfect A D).ι ⋙ ScalarExtension.derivedExtension φ D ⋙
        dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D) (ScalarExtension.DGBaseChange φ E)
          (ScalarExtension.dgFunctor φ F) := by
  let e := perfectDGModuleHomotopyEquivalence A D Set.univ
  let L := dgDerivedExtension A D E F ⋙ ScalarExtension.derivedExtension φ E
  let R := ScalarExtension.derivedExtension φ D ⋙
    dgDerivedExtension A' (ScalarExtension.DGBaseChange φ D) (ScalarExtension.DGBaseChange φ E)
      (ScalarExtension.dgFunctor φ F)
  exact
    isoWhiskerRight e.counitIso.symm ((modulePerfect A D).ι ⋙ L) ≪≫
    isoWhiskerLeft e.inverse (scalarGraphPerfectHomotopySquare φ D E F) ≪≫
    isoWhiskerRight e.counitIso ((modulePerfect A D).ι ⋙ R)
end SerrePositivity.DifferentialGraded
