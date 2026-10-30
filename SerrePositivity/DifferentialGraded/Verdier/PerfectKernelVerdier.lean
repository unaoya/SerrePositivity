module
public import SerrePositivity.DifferentialGraded.Verdier.KernelActionTriangles
public import SerrePositivity.CategoryTheory.Triangulated.VerdierLift
public import SerrePositivity.CategoryTheory.Karoubi.Triangulated

/-! # 指定生成集合を対応させる主導来 kernel の実際の Perf–Verdier 関手 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Limits Idempotents Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全 Perf の中で、指定集合 S から生成される厚い零対象クラス。 -/
def perfectNullObjects (S : Set D) : ObjectProperty (PerfectModuleCategory A D) :=
  (modulePerfectOver A D S).inverseImage (modulePerfectOver A D Set.univ).ι

instance perfectNullObjectsIsTriangulated (S : Set D) :
    (perfectNullObjects A D S).IsTriangulated := by
  dsimp [perfectNullObjects]
  infer_instance

abbrev PerfectVerdierQuotient (S : Set D) := (perfectNullObjects A D S).trW.Localization
abbrev perfectVerdierQuotient (S : Set D) :
    PerfectModuleCategory A D ⥤ PerfectVerdierQuotient A D S :=
  (perfectNullObjects A D S).trW.Q

variable (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)
  (hK : kernelColumnsPerfect A D E K) (S : Set D) (T : Set E)
  (hST : ∀ d ∈ S, modulePerfectOver A E T ((kernelDerivedColumn A D E d).obj K))

local instance perfectKernelVerdierShift : (perfectDerivedKernelAction A D E K hK).CommShift ℤ :=
  mainPerfectKernelActionCommShift A D E K hK
local instance perfectKernelVerdierTriangles :
    (perfectDerivedKernelAction A D E K hK).IsTriangulated :=
  mainPerfectKernelActionIsTriangulated A D E K hK

include hST in
lemma perfectKernelNullObjects_image (X : PerfectModuleCategory A D)
    (hX : perfectNullObjects A D S X) :
    perfectNullObjects A E T ((perfectDerivedKernelAction A D E K hK).obj X) :=
  mainKernelAction_perfectOver A D E K S T hST hX

include hST in
lemma perfectKernelVerdier_kills (X : PerfectModuleCategory A D) (hX : perfectNullObjects A D S X) :
    IsZero ((perfectVerdierQuotient A E T).obj
      ((perfectDerivedKernelAction A D E K hK).obj X)) :=
  verdierQuotient_isZero (perfectNullObjects A E T) _
    (perfectKernelNullObjects_image A D E K hK S T hST X hX)

/-- 元の実際の主 Perf 作用を先に Verdier 局所化して得る関手。 -/
def perfectKernelVerdierFunctor : PerfectVerdierQuotient A D S ⥤ PerfectVerdierQuotient A E T :=
  verdierLift (perfectNullObjects A D S)
    (perfectDerivedKernelAction A D E K hK ⋙ perfectVerdierQuotient A E T)
    (perfectKernelVerdier_kills A D E K hK S T hST)

/-- 主導来 kernel の Perf 作用と標準商関手の実際の因子化正方形。 -/
def perfectKernelVerdierSquare :
    perfectVerdierQuotient A D S ⋙ perfectKernelVerdierFunctor A D E K hK S T hST ≅
      perfectDerivedKernelAction A D E K hK ⋙ perfectVerdierQuotient A E T :=
  verdierLiftFactors _ _ (perfectKernelVerdier_kills A D E K hK S T hST)

instance perfectKernelVerdierFunctorCommShift :
    (perfectKernelVerdierFunctor A D E K hK S T hST).CommShift ℤ := by
  dsimp [perfectKernelVerdierFunctor]
  infer_instance
instance perfectKernelVerdierSquareCommShift :
    NatTrans.CommShift (perfectKernelVerdierSquare A D E K hK S T hST).hom ℤ := by
  dsimp [perfectKernelVerdierSquare]
  infer_instance
instance perfectKernelVerdierFunctorIsTriangulated :
    (perfectKernelVerdierFunctor A D E K hK S T hST).IsTriangulated := by
  dsimp [perfectKernelVerdierFunctor]
  infer_instance

def perfectKernelCompletedVerdierFunctor :
    Karoubi (PerfectVerdierQuotient A D S) ⥤ Karoubi (PerfectVerdierQuotient A E T) :=
  (functorExtension₂ _ _).obj (perfectKernelVerdierFunctor A D E K hK S T hST)

def perfectKernelVerdierSquareTriangle :=
  Functor.mapTriangleIso (perfectKernelVerdierSquare A D E K hK S T hST)
end SerrePositivity.DifferentialGraded
