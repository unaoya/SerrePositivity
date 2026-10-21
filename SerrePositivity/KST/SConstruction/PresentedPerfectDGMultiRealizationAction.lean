module
public import SerrePositivity.KST.SConstruction.DiagonalParameterizedEvaluation
public import SerrePositivity.KST.SConstruction.InternalEnrichedActionLaws
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGMultiRealizationEnrichedFunctor

/-! # 元の反復実現への全 native dg 作用
概要：元の全反復実現の作用を明示し、各段の元の全作用と同定する。
方針：標準 end の各射影の回収と対角評価を合成する。
規約：全 Kan 入力を保持する。使われ方：全零境界の保存と同じ点つき商への降下。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ元の全反復実現の実値を、具体的な既存の模型として明示する。 -/
def presentedPerfectDGMultiRealizationValue (r : ℕ) (C : PerfDGInput.{u, v} A) :
    SSet.{max (u + 1) v} :=
  multiDiagonalCoreSConstruction r
    (stableCategoryModel (presentedPerfectDGStableCategory A C))

/-- 同じ元の全反復実現に対する、全 native Kan dg 入力族の実作用。 -/
def presentedPerfectDGMultiRealizationAction (r : ℕ) (C D : PerfDGInput.{u, v} A) :
    (presentedPerfectDGMultiRealizationValue A r C) ⊗
      (C ⟶[SSet.{max (u + 1) v}] D) ⟶
        (presentedPerfectDGMultiRealizationValue A r D) :=
  uncurry ((presentedPerfectDGMultiRealizationEnrichedFunctor A r).map C D)

/-- 各次数の実現作用は、元の同じ多次数の全 native core 作用。 -/
lemma presentedPerfectDGMultiRealizationAction_app (r : ℕ)
    (C D : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ)
    (x : (presentedPerfectDGMultiRealizationValue A r C).obj n)
    (p : (C ⟶[SSet.{max (u + 1) v}] D).obj n) :
    (presentedPerfectDGMultiRealizationAction A r C D).app n (x, p) =
      (uncurry (((presentedPerfectDGMultiSCoreEnrichedDiagram A r).obj (fun _ => n)).map
        C D)).app n (x, p) := by
  have h := congrArg (uncurry (C := SSet.{max (u + 1) v}))
    (presentedPerfectDGMultiSCoreObjectEnrichedFunctor_projection A r C D n)
  exact (simplicialSSetDiagramDiagonal_parameter_app
    ((presentedPerfectDGMultiSCoreObjectEnrichedFunctor A r).map C D) n x p).trans
      (congrArg (fun q => q.app n (x, p)) h)

/-- 元の native 豊穣恒等入力は、同じ反復実現の恒等作用。 -/
lemma presentedPerfectDGMultiRealizationAction_unit (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (𝟙 (presentedPerfectDGMultiRealizationValue A r C) ⊗ₘ
      eId SSet.{max (u + 1) v} C) ≫ presentedPerfectDGMultiRealizationAction A r C C =
        (ρ_ (presentedPerfectDGMultiRealizationValue A r C)).hom :=
  internalEnrichedAction_unit (presentedPerfectDGMultiRealizationEnrichedFunctor A r) C

/-- 二回の元の実現作用は、同じ native dg 合成による作用に厳密に一致。 -/
lemma presentedPerfectDGMultiRealizationAction_comp (r : ℕ) (C D E : PerfDGInput.{u, v} A) :
    (presentedPerfectDGMultiRealizationAction A r C D ⊗ₘ
      𝟙 (D ⟶[SSet.{max (u + 1) v}] E)) ≫ presentedPerfectDGMultiRealizationAction A r D E =
      (α_ (presentedPerfectDGMultiRealizationValue A r C)
        (C ⟶[SSet.{max (u + 1) v}] D) (D ⟶[SSet.{max (u + 1) v}] E)).hom ≫
          (𝟙 _ ⊗ₘ eComp SSet.{max (u + 1) v} C D E) ≫
            presentedPerfectDGMultiRealizationAction A r C E :=
  internalEnrichedAction_comp (presentedPerfectDGMultiRealizationEnrichedFunctor A r) C D E

/-- 元の通常 dg 射では、同じ元の反復実現の射を全作用から回収する。 -/
lemma presentedPerfectDGMultiRealizationAction_hom (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    (𝟙 (presentedPerfectDGMultiRealizationValue A r C) ⊗ₘ
      eHomEquiv SSet.{max (u + 1) v} F) ≫ presentedPerfectDGMultiRealizationAction A r C D =
        (ρ_ (presentedPerfectDGMultiRealizationValue A r C)).hom ≫
          (multiRealizationFunctor r).map
            (show stableCategoryModel (presentedPerfectDGStableCategory A C) ⟶
              stableCategoryModel (presentedPerfectDGStableCategory A D) from
                ⟨(presentedPerfectDGExactMap A F).hom,
                  preservesCofiberData_of_isExactFunctor (presentedPerfectDGExactMap A F).hom⟩) :=
  internalEnrichedAction_hom (presentedPerfectDGMultiRealizationEnrichedFunctor A r) F _
    (presentedPerfectDGMultiRealizationEnrichedFunctor_hom A r F)

end SerrePositivity.KST.SConstruction
