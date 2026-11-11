module
public import SerrePositivity.KST.SConstruction.InternalEnrichedActionLaws
public import SerrePositivity.KST.SConstruction.ClosedFamilyHomEvaluation
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionBoundaryAction
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionEnrichedFunctor

/-! # 一次方向の元の全 native dg 作用の法則
概要：元の一次方向実現の単位・合成・通常射の回収を証明する。
方針：同じ元の作用を持つ閉 Hom 値豊穣関手の法則を評価する。
規約：全 Kan 入力を保持する。使われ方：全零境界の保存と同じ点つき商への降下。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の native 豊穣恒等入力は、同じ反復実現の恒等作用。 -/
lemma presentedPerfectDGOneDirectionAction_unit (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (𝟙 ((oneDirectionRealizationFunctor r).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C))) ⊗ₘ
      eId SSet.{max (u + 1) v} C) ≫ presentedPerfectDGOneDirectionAction A r C C =
        (ρ_ ((oneDirectionRealizationFunctor r).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C)))).hom :=
  internalEnrichedAction_unit (presentedPerfectDGOneDirectionEnrichedFunctor A r) C

/-- 二回の元の実現作用は、同じ native dg 合成による作用に厳密に一致。 -/
lemma presentedPerfectDGOneDirectionAction_comp (r : ℕ) (C D E : PerfDGInput.{u, v} A) :
    (presentedPerfectDGOneDirectionAction A r C D ⊗ₘ
      𝟙 (D ⟶[SSet.{max (u + 1) v}] E)) ≫ presentedPerfectDGOneDirectionAction A r D E =
      (α_ ((oneDirectionRealizationFunctor r).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C)))
        (C ⟶[SSet.{max (u + 1) v}] D) (D ⟶[SSet.{max (u + 1) v}] E)).hom ≫
          (𝟙 _ ⊗ₘ eComp SSet.{max (u + 1) v} C D E) ≫
            presentedPerfectDGOneDirectionAction A r C E := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  let G := (presentedPerfectDGMultiSCoreEnrichedDiagram A (r + 1)).obj
    ((oneDirectionIndex r).obj (fun _ => n))
  have h₁ := presentedPerfectDGOneDirectionAction_app A r C D n z.1.1 z.1.2
  have h₂ := presentedPerfectDGOneDirectionAction_app A r D E n
    ((presentedPerfectDGOneDirectionAction A r C D).app n z.1) z.2
  have h₃ := presentedPerfectDGOneDirectionAction_app A r C E n z.1.1
    ((eComp SSet.{max (u + 1) v} C D E).app n (z.1.2, z.2))
  have hn := types_congr_hom (NatTrans.congr_app
    (quasicategoryEnrichedAction_comp G C D E) n) z
  exact h₂.trans ((congrArg (fun x => (uncurry (G.map D E)).app n (x, z.2)) h₁).trans
    (hn.trans h₃.symm))

/-- 元の通常 dg 射では、同じ元の反復実現の射を全作用から回収する。 -/
lemma presentedPerfectDGOneDirectionAction_hom (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    (𝟙 ((oneDirectionRealizationFunctor r).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C))) ⊗ₘ
      eHomEquiv SSet.{max (u + 1) v} F) ≫ presentedPerfectDGOneDirectionAction A r C D =
        (ρ_ ((oneDirectionRealizationFunctor r).obj
      (stableCategoryModel (presentedPerfectDGStableCategory A C)))).hom ≫
          (oneDirectionRealizationFunctor r).map
            (show stableCategoryModel (presentedPerfectDGStableCategory A C) ⟶
              stableCategoryModel (presentedPerfectDGStableCategory A D) from
                ⟨(presentedPerfectDGExactMap A F).hom,
                  preservesCofiberData_of_isExactFunctor
                    (presentedPerfectDGExactMap A F).hom⟩) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  let d := (oneDirectionIndex r).obj (fun _ => n)
  let G := (presentedPerfectDGMultiSCoreEnrichedDiagram A (r + 1)).obj d
  have h := presentedPerfectDGMultiSCoreEnrichedDiagram_hom A (r + 1) d F
  have he := closedFamily_hom_action
    (X := (G.obj C).obj) (Y := (G.obj D).obj)
    (P := C ⟶[SSet.{max (u + 1) v}] D)
    (eHomEquiv SSet.{max (u + 1) v} F) (G.map C D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (multiSExactMap (r + 1) d (presentedPerfectDGExactMap A F)).hom) h
  exact (presentedPerfectDGOneDirectionAction_app A r C D n z.1
    ((eHomEquiv SSet.{max (u + 1) v} F).app n z.2)).trans
      (types_congr_hom (NatTrans.congr_app he n) z)

end SerrePositivity.KST.SConstruction
