module
public import SerrePositivity.DifferentialGraded.Module.GradedCoproduct
public import SerrePositivity.DifferentialGraded.Module.Cells
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # 証明付きsemifree filtration

自由sphere余積の表示、全斉次作用に関する分裂、余極限の網羅性をデータとして保持する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- u-smallな自由sphere余積としての具体的表示。添字のambient宇宙はmax u v。 -/
structure ModuleSphereFreePresentation (M : ModuleCategory A D) where
  Index : Type (max u v)
  [smallIndex : Small.{u} Index]
  object : Index → D
  degree : Index → ℤ
  iso : M ≅ ∐ (fun t => freeSphere A D (object t) (degree t))

/-- 初期段と各商が自由sphere余積であり、全次数で分裂する網羅的filtration。 -/
structure ModuleSemifreeFiltration (M : ModuleCategory A D) where
  stage : ℕ → ModuleCategory A D
  transition : ∀ n, stage n ⟶ stage (n + 1)
  initial : ModuleSphereFreePresentation A D (stage 0)
  quotient : ℕ → ModuleCategory A D
  quotientMap : ∀ n, stage (n + 1) ⟶ quotient n
  split : ∀ n, ModuleGradedSplit A D (transition n) (quotientMap n)
  quotientPresentation : ∀ n, ModuleSphereFreePresentation A D (quotient n)
  cocone : Cocone (Functor.ofSequence transition)
  isColimit : IsColimit cocone
  iso : cocone.pt ≅ M

/-- この主dg加群はsemifree filtrationを持つ。 -/
def moduleSemifree : ObjectProperty (ModuleCategory A D) :=
  fun M => Nonempty (ModuleSemifreeFiltration A D M)

/-- 各商は主圏での真のcokernelであり、単なる次数付き表示ではない。 -/
def ModuleSemifreeFiltration.stepCokernel {M : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (F.quotientMap n) (F.split n).inclusion_projection) :=
  moduleGradedSplitCokernel A D (F.split n)

end SerrePositivity.DifferentialGraded
