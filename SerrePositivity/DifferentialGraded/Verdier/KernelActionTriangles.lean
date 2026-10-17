module
public import SerrePositivity.DifferentialGraded.Verdier.ProjectiveResolutionComparison
public import SerrePositivity.DifferentialGraded.Morita.PerfectKernelColumns
public import SerrePositivity.DifferentialGraded.Endomorphism.ConeTriangleComparison

/-! # 主導来 kernel の実際の作用の三角性

任意の通常 kernel の tensor dg 関手を射影的ホモトピー圏上で計算し、
既存の入力解像度による作用との自然同型で構造を運ぶ。dg 圏の分解を使わない。
-/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

local instance kernelTrianglesHomotopyCommShift : (kernelTensor A D E P).onHomotopy.CommShift ℤ :=
  dgModuleFunctorHomotopyCommShift A D E (kernelTensor A D E P)
local instance kernelTrianglesHomotopyIsTriangulated :
    (kernelTensor A D E P).onHomotopy.IsTriangulated :=
  dgModuleFunctorHomotopyIsTriangulated A D E (kernelTensor A D E P)

def kernelProjectiveActionModel : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E :=
  (projectiveModuleDerivedEquivalence A D).inverse ⋙ (moduleHomotopyProjectiveLocus A D).ι ⋙
    (kernelTensor A D E P).onHomotopy ⋙ moduleHomotopyToDerivedClosed A E

instance kernelProjectiveActionModelCommShift :
    (kernelProjectiveActionModel A D E P).CommShift ℤ := by
  dsimp [kernelProjectiveActionModel]
  infer_instance
instance kernelProjectiveActionModelIsTriangulated :
    (kernelProjectiveActionModel A D E P).IsTriangulated := by
  dsimp [kernelProjectiveActionModel]
  infer_instance

/-- 入力解像度による実際の作用と、射影的ホモトピー圏上の計算の自然同型。 -/
def kernelProjectiveActionComparison :
    kernelDerivedTensorOnBimodule A D E P ≅ kernelProjectiveActionModel A D E P :=
  isoWhiskerRight
    (derivedResolutionProjectiveComparison A D (moduleCanonicalProjectiveResolution A D))
    (kernelHomotopyToDerived A D E P) ≪≫ Functor.associator _ _ _

/-- まだ構造を持たない実作用に、実際の tensor dg 関手から shift 構造を与える。 -/
@[instance_reducible]
def kernelOnBimoduleActionCommShift : (kernelDerivedTensorOnBimodule A D E P).CommShift ℤ :=
  Functor.CommShift.ofIso (kernelProjectiveActionComparison A D E P).symm ℤ

lemma kernelOnBimoduleActionIsTriangulated :
    letI := kernelOnBimoduleActionCommShift A D E P
    (kernelDerivedTensorOnBimodule A D E P).IsTriangulated := by
  let := kernelOnBimoduleActionCommShift A D E P
  let := Functor.CommShift.ofIso_compatibility (kernelProjectiveActionComparison A D E P).symm ℤ
  exact Functor.isTriangulated_of_iso (kernelProjectiveActionComparison A D E P).symm

variable (K : Kernel A D E)

/-- 主局所化上の kernel の作用にも、同じ計算から整数 shift を与える。 -/
@[instance_reducible]
def mainKernelActionCommShift : (kernelDerivedTensor A D E K).CommShift ℤ := by
  obtain ⟨⟨Q⟩⟩ := K
  letI := kernelOnBimoduleActionCommShift A D E (BimoduleCategory.underlying A E D Q)
  exact Functor.CommShift.ofIso (kernelDerivedTensorOnBimoduleIso A D E Q).symm ℤ

lemma mainKernelActionIsTriangulated :
    letI := mainKernelActionCommShift A D E K
    (kernelDerivedTensor A D E K).IsTriangulated := by
  obtain ⟨⟨Q⟩⟩ := K
  let := kernelOnBimoduleActionCommShift A D E (BimoduleCategory.underlying A E D Q)
  let := kernelOnBimoduleActionIsTriangulated A D E (BimoduleCategory.underlying A E D Q)
  let := mainKernelActionCommShift A D E ((bimoduleToDerived A E D).obj Q)
  let := Functor.CommShift.ofIso_compatibility (kernelDerivedTensorOnBimoduleIso A D E Q).symm ℤ
  exact Functor.isTriangulated_of_iso (kernelDerivedTensorOnBimoduleIso A D E Q).symm

@[instance_reducible]
def mainPerfectKernelActionCommShift (hK : kernelColumnsPerfect A D E K) :
    (perfectDerivedKernelAction A D E K hK).CommShift ℤ := by
  letI := mainKernelActionCommShift A D E K
  dsimp [perfectDerivedKernelAction, perfectFunctorRestriction, perfectModuleInclusion]
  infer_instance

lemma mainPerfectKernelActionIsTriangulated (hK : kernelColumnsPerfect A D E K) :
    letI := mainPerfectKernelActionCommShift A D E K hK
    (perfectDerivedKernelAction A D E K hK).IsTriangulated := by
  let := mainKernelActionCommShift A D E K
  let := mainKernelActionIsTriangulated A D E K
  dsimp [mainPerfectKernelActionCommShift, perfectDerivedKernelAction,
    perfectFunctorRestriction, perfectModuleInclusion]
  infer_instance

/-- 指定列の Perf 条件から、殺す生成集合の thick 閉包の像を判定する。 -/
lemma mainKernelAction_perfectOver (S : Set D) (T : Set E)
    (hST : ∀ d ∈ S, modulePerfectOver A E T ((kernelDerivedColumn A D E d).obj K))
    {X : DerivedModuleCategory A D} (hX : modulePerfectOver A D S X) :
    modulePerfectOver A E T ((kernelDerivedTensor A D E K).obj X) := by
  let := mainKernelActionCommShift A D E K
  let := mainKernelActionIsTriangulated A D E K
  let N := (modulePerfectOver A E T).inverseImage (kernelDerivedTensor A D E K)
  have : N.IsTriangulated := by dsimp [N]; infer_instance
  have : N.IsClosedUnderIsomorphisms := by dsimp [N]; infer_instance
  have : N.IsStableUnderRetracts :=
    ⟨fun r hY => (modulePerfectOver A E T).prop_of_retract
      (r.map (kernelDerivedTensor A D E K)) hY⟩
  exact ((modulePerfectOver_le_iff_generators A D N S).2 (fun d hd =>
    (modulePerfectOver A E T).prop_of_iso (kernelDerivedColumnActionIso A D E K d).symm
      (hST d hd))) X hX
end SerrePositivity.DifferentialGraded
