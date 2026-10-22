module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DecompositionCFactorIso
public import SerrePositivity.InfinityCategories.Derived.Gluing.RepresentableConeTriangle

/-! 実 D 余単位を第一射に持つ、D 切断→元の対象→C 切断の代表加群分解三角形。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Pretriangulated DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
  (X : DGGluingObject R C D M)
local notation "G" => DGGluingObject R C D M
local notation "K" => moduleToHomotopy R G
local notation "A" => dgGluingDecompositionDSource R C D M hC X
local notation "f" => dgGluingDecompositionArrow R C D M hC X
local notation "W" => dgGluingDecompositionCFactor R C D M hC hD X

/-- 元の左射影を同じ C 切断で戻した実対象。 -/
def dgGluingDecompositionCSource : G :=
  ForgetEnrichment.to (Complex R)
    ((dgGluingCSectionHomotopy R C D M hD).obj ((dgGluingLeft R C D M).onHomotopy.obj
      ((toHomotopy R G).obj (ForgetEnrichment.of (Complex R) X)))).as

/-- 元の同じ H⁰ 同型の Yoneda 像としての、C 切断と円錐代表の K 同型。 -/
def dgGluingDecompositionCModuleIso :
    (K).obj (ForgetEnrichment.of (Complex R)
      (representable R (dgGluingDecompositionCSource R C D M hD X))) ≅
      (K).obj (ForgetEnrichment.of (Complex R) (representable R (W).val)) :=
  (dgYoneda R G).onHomotopy.mapIso (dgGluingDecompositionCSectionIso R C D M hC hD X)

/-- 同じ実 D 余単位の円錐を C 充満因子の代表として持つ分解三角形。 -/
def dgGluingDecompositionFactorTriangle : Triangle (ModuleHomotopyCategory R G) :=
  dgGluingRepresentableConeTriangle R C D M A X f hC hD

lemma dgGluingDecompositionFactorTriangle_distinguished :
    dgGluingDecompositionFactorTriangle R C D M hC hD X ∈
      distTriang (ModuleHomotopyCategory R G) :=
  dgGluingRepresentableConeTriangle_distinguished R C D M A X f hC hD

/-- 同じ第一射と第二対象を保持し、第三対象を元の C 切断へ同定した実分解三角形。 -/
def dgGluingDecompositionTriangle : Triangle (ModuleHomotopyCategory R G) :=
  dgGluingTriangleThirdTransport
    (dgGluingDecompositionFactorTriangle R C D M hC hD X)
    (dgGluingDecompositionCModuleIso R C D M hC hD X).symm

lemma dgGluingDecompositionTriangle_distinguished :
    dgGluingDecompositionTriangle R C D M hC hD X ∈
      distTriang (ModuleHomotopyCategory R G) :=
  dgGluingTriangleThirdTransport_distinguished
    (dgGluingDecompositionFactorTriangle R C D M hC hD X)
    (dgGluingDecompositionFactorTriangle_distinguished R C D M hC hD X)
    (dgGluingDecompositionCModuleIso R C D M hC hD X).symm

lemma dgGluingDecompositionTriangle_obj₁ :
    (dgGluingDecompositionTriangle R C D M hC hD X).obj₁ =
      (K).obj (ForgetEnrichment.of (Complex R) (representable R A)) := rfl

lemma dgGluingDecompositionTriangle_obj₂ :
    (dgGluingDecompositionTriangle R C D M hC hD X).obj₂ =
      (K).obj (ForgetEnrichment.of (Complex R) (representable R X)) := rfl

lemma dgGluingDecompositionTriangle_obj₃ :
    (dgGluingDecompositionTriangle R C D M hC hD X).obj₃ =
      (K).obj (ForgetEnrichment.of (Complex R)
        (representable R (dgGluingDecompositionCSource R C D M hD X))) := rfl

/-- 分解三角形の第一射は、選択に依らず同じ D 随伴余単位の Yoneda 像。 -/
lemma dgGluingDecompositionTriangle_mor₁ :
    (dgGluingDecompositionTriangle R C D M hC hD X).mor₁ =
      (dgYoneda R G).onHomotopy.map
        ((dgGluingDProjectionAdjunction R C D M hC).counit.app
          ((toHomotopy R G).obj (ForgetEnrichment.of (Complex R) X))) := by
  change (dgYoneda R G).onHomotopy.map
    ((toHomotopy R G).map (dgGluingDecompositionArrow R C D M hC X)) = _
  rw [dgGluingDecompositionArrow_map]

end SerrePositivity.InfinityCategories
