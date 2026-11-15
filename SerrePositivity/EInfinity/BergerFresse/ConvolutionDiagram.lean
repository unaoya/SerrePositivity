module

public import SerrePositivity.EInfinity.SimplexCuts.Coalgebra
public import SerrePositivity.EInfinity.BarrattEccles.DiscreteAlgebra
public import SerrePositivity.EInfinity.BarrattEccles.Hopf
public import SerrePositivity.EInfinity.Operad.ConvolutionFunctor
public import SerrePositivity.EInfinity.Operad.AlgebraLimits
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# 元のBF単体余代数からのconvolution図式

Berger–Fresse §2.2・§3.1、M14 L22、報告 §401。
元のUnder値の入力と全単体射を保ち、既存の前後合成を束ねる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BergerFresse
open CategoryTheory Limits
open SerrePositivity.Cosimplicial (CosimplicialAlgebra)
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 元の全有限次元の単体射の添字（BF §2.2）。 -/
abbrev SimplexMorphismIndex := Σ q r : ℕ, (⦋q⦌ : SimplexCategory) ⟶ ⦋r⦌

/-- 元のUnder入力を同じ離散BE代数へ読む（BF §3.1）。 -/
def discreteUnderFunctor : Under (CommRingCat.of A) ⥤ (BarrattEccles.operad A).Algebra :=
  (commAlgCatEquivUnder (CommRingCat.of A)).inverse ⋙ BarrattEccles.discreteAlgebraFunctor A

/-- 同じ一般次元のBF単体余代数の関手（BF §2.2・§3.1）。 -/
def simplexCoalgebraFunctor : SimplexCategory ⥤ (BarrattEccles.operad A).Coalgebra :=
  SSet.stdSimplex ⋙ SimplexCuts.barrattEcclesCoalgebraFunctor A

/-- 同じq単体余代数から離散Under入力へのconvolution関手（BF §3.1）。 -/
def convolutionOnUnder (q : ℕ) : Under (CommRingCat.of A) ⥤ (BarrattEccles.operad A).Algebra :=
  discreteUnderFunctor A ⋙ Operad.convolutionFunctor (BarrattEccles.hopf A)
    ((simplexCoalgebraFunctor A).obj ⦋q⦌)

/-- 元の第r項をq単体からのconvolutionへ送る（BF §3.1）。 -/
def convolutionAt (q r : ℕ) : CosimplicialAlgebra A ⥤ (BarrattEccles.operad A).Algebra :=
  (evaluation SimplexCategory (Under (CommRingCat.of A))).obj ⦋r⦌ ⋙ convolutionOnUnder A q

/-- 元の余単体射による後合成は全入力で自然（BF §3.1）。 -/
def postAt {q r : ℕ} (α : (⦋q⦌ : SimplexCategory) ⟶ ⦋r⦌) :
    convolutionAt A q q ⟶ convolutionAt A q r where
  app X := (convolutionOnUnder A q).map (X.map α)
  naturality := by
    intro X Y f
    change (convolutionOnUnder A q).map (f.app ⦋q⦌) ≫
        (convolutionOnUnder A q).map (Y.map α) =
      (convolutionOnUnder A q).map (X.map α) ≫ (convolutionOnUnder A q).map (f.app ⦋r⦌)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (convolutionOnUnder A q).map (f.naturality α).symm

/-- 元の単体余代数の射による前合成は全入力で自然（BF §3.1）。 -/
def preAt {q r : ℕ} (α : (⦋q⦌ : SimplexCategory) ⟶ ⦋r⦌) :
    convolutionAt A r r ⟶ convolutionAt A q r where
  app X := Operad.convolutionPre (BarrattEccles.hopf A) ((simplexCoalgebraFunctor A).map α)
    ((discreteUnderFunctor A).obj (X.obj ⦋r⦌))
  naturality := by
    intro X Y f
    exact (Operad.convolutionPreNat (BarrattEccles.hopf A)
      ((simplexCoalgebraFunctor A).map α)).naturality ((discreteUnderFunctor A).map (f.app ⦋r⦌))

end SerrePositivity.EInfinity.BergerFresse
