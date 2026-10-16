module
public import SerrePositivity.DifferentialGraded.Perfect.RingSingleShift
public import SerrePositivity.DifferentialGraded.Derived.EvaluationTriangles
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # 通常複体の短完全列による主導来perfect性の拡張

既存の一対象導来同値で通常の短完全列の三角形を主導来圏へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex MonoidalCategory Pretriangulated
variable (A : Type u) [CommRing A]

/-- 実際のdg関手の合成比較から、通常複体の評価比較を得る。 -/
def complexToRingModuleEvaluationIso :
    complexToRingModule A ⋙ moduleEvaluation A PUnit.{1} PUnit.unit ≅ 𝟭 (Complex A) := by
  let I := ForgetEnrichment.equivInverse (Complex A) (Complex A)
  let C := (ringConstantDG A).onClosed
  let V := (moduleEvaluationDG A PUnit.{1} PUnit.unit).onClosed
  let E := closedToComplex A
  let h : C ⋙ V ≅ 𝟭 (ClosedCategory A (Complex A)) :=
    (EnrichedFunctor.forgetComp (ringConstantDG A)
      (moduleEvaluationDG A PUnit.{1} PUnit.unit)).symm ≪≫
    eqToIso (congrArg (fun F => DGFunctor.onClosed F) (ringConstantDG_comp_evaluation A)) ≪≫
    EnrichedFunctor.forgetId (Complex A) (Complex A)
  exact Functor.associator I C (V ⋙ E) ≪≫
    Functor.isoWhiskerLeft I ((Functor.associator C V E).symm ≪≫
      Functor.isoWhiskerRight h E ≪≫ Functor.leftUnitor E) ≪≫
    (ForgetEnrichment.equiv (Complex A) (D := Complex A)).counitIso

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 主導来像を一対象導来同値で評価すると既存Qと自然同型で一致する。 -/
def complexToRingModuleDerivedEvaluationIso :
    (complexToRingModule A ⋙ moduleToDerived A PUnit.{1}) ⋙
      (ringDerivedEquivalence A).functor ≅ DerivedCategory.Q (C := ModuleCat.{u} A) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (complexToRingModule A) (ringDerivedEquivalence_fac A) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (complexToRingModuleEvaluationIso A) DerivedCategory.Q ≪≫
    Functor.leftUnitor _

/-- 既存導来圏の通常複体の像を同値の逆で戻すと、実際の主dg加群の像と一致する。 -/
def ringComplexDerivedUnitIso (P : Complex A) :
    (ringDerivedEquivalence A).inverse.obj (DerivedCategory.Q.obj P) ≅
      (moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P) :=
  (ringDerivedEquivalence A).inverse.mapIso
      ((complexToRingModuleDerivedEvaluationIso A).app P).symm ≪≫
    ((ringDerivedEquivalence A).unitIso.app _).symm

/-- 通常複体の短完全列の両端の主導来像がperfectなら中央もperfect。 -/
lemma ringComplexDerived_perfect_of_shortExact (S : ShortComplex (Complex A))
    (hS : S.ShortExact)
    (h₁ : modulePerfect A PUnit.{1}
      ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj S.X₁)))
    (h₃ : modulePerfect A PUnit.{1}
      ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj S.X₃))) :
    modulePerfect A PUnit.{1}
      ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj S.X₂)) := by
  let E := ringDerivedEquivalence A
  let T := E.inverse.mapTriangle.obj (DerivedCategory.triangleOfSES hS)
  have hT : T ∈ distTriang (DerivedModuleCategory A PUnit.{1}) :=
    E.inverse.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS)
  exact (modulePerfect A PUnit.{1}).prop_of_iso (ringComplexDerivedUnitIso A S.X₂)
    (modulePerfectOver_triangle_obj₂ A PUnit.{1} Set.univ T hT
      ((modulePerfect A PUnit.{1}).prop_of_iso (ringComplexDerivedUnitIso A S.X₁).symm h₁)
      ((modulePerfect A PUnit.{1}).prop_of_iso (ringComplexDerivedUnitIso A S.X₃).symm h₃))

end SerrePositivity.DifferentialGraded
