module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Coalgebra
public import SerrePositivity.EInfinity.BarrattEccles.DiscreteAlgebra
public import SerrePositivity.EInfinity.BarrattEccles.Hopf
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionFunctor
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraLimits
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
模型。文献の定義との比較は後で
# 元のBF単体余代数からのconvolution図式

Berger–Fresse §2.2・§3.1、M14 L22、報告 §401。
元のUnder値の入力と全単体射を保ち、既存の前後合成を束ねる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.Cosimplicial (CosimplicialAlgebra)
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- 元の全有限次元の単体射の添字（BF §2.2）。 -/
abbrev SimplexMorphismIndex := Σ q r : ℕ, (⦋q⦌ : SimplexCategory) ⟶ ⦋r⦌

/-- 元のUnder入力を同じ離散BE代数へ読む（BF §3.1）。 -/
def discreteUnderFunctor : Under (CommRingCat.of A) ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra :=
  (commAlgCatEquivUnder (CommRingCat.of A)).inverse ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.discreteAlgebraFunctor A

/-- 同じ一般次元のBF単体余代数の関手（BF §2.2・§3.1）。 -/
def simplexCoalgebraFunctor : SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Coalgebra :=
  SSet.stdSimplex ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.barrattEcclesCoalgebraFunctor A

/-- 同じq単体余代数から離散Under入力へのconvolution関手（BF §3.1）。 -/
def convolutionOnUnder (q : ℕ) : Under (CommRingCat.of A) ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.discreteUnderFunctor A ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionFunctor (_root_.SerrePositivity.EInfinity.BarrattEccles.hopf A)
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.simplexCoalgebraFunctor A).obj ⦋q⦌)

/-- 元の第r項をq単体からのconvolutionへ送る（BF §3.1）。 -/
def convolutionAt (q r : ℕ) : CosimplicialAlgebra A ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra :=
  (evaluation SimplexCategory (Under (CommRingCat.of A))).obj ⦋r⦌ ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionOnUnder A q

/-- 元の余単体射による後合成は全入力で自然（BF §3.1）。 -/
def postAt {q r : ℕ} (α : (⦋q⦌ : SimplexCategory) ⟶ ⦋r⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionAt A q q ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionAt A q r where
  app X := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionOnUnder A q).map (X.map α)
  naturality := by
    intro X Y f
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionOnUnder A q).map (f.app ⦋q⦌) ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionOnUnder A q).map (Y.map α) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionOnUnder A q).map (X.map α) ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionOnUnder A q).map (f.app ⦋r⦌)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionOnUnder A q).map (f.naturality α).symm

/-- 元の単体余代数の射による前合成は全入力で自然（BF §3.1）。 -/
def preAt {q r : ℕ} (α : (⦋q⦌ : SimplexCategory) ⟶ ⦋r⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionAt A r r ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.convolutionAt A q r where
  app X := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionPre (_root_.SerrePositivity.EInfinity.BarrattEccles.hopf A) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.simplexCoalgebraFunctor A).map α)
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.discreteUnderFunctor A).obj (X.obj ⦋r⦌))
  naturality := by
    intro X Y f
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionPreNat (_root_.SerrePositivity.EInfinity.BarrattEccles.hopf A)
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.simplexCoalgebraFunctor A).map α)).naturality ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse.discreteUnderFunctor A).map (f.app ⦋r⦌))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.BergerFresse
