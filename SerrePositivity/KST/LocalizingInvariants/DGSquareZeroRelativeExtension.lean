module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeHomotopyPullback
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroExtensionHomology
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitness

/-!
概要：平方零 class の底を固定した実拡大模型と、元の絶対模型への準同型比較。
方針：相対 mapping-path と零切断の実 pullback を使い、元の二脚と経路を保つ。
規約：class の底への射影が次数全射なら比較は準同型。使われ方：相対 class 経路の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} (N : Bimod A A)
  (a : W ⟶ SquareZero.algebra A N)

def relativeModel : Mon (Complex R) := DGAlgebra.RelativeHomotopyPullback.algebra R
  (SquareZero.projection A N) a (SquareZero.zeroSection A N)

def relativeLeft : relativeModel N a ⟶ W := DGAlgebra.RelativeHomotopyPullback.left R _ _ _
def relativeRight : relativeModel N a ⟶ A := DGAlgebra.RelativeHomotopyPullback.right R _ _ _
def relativePath : relativeModel N a ⟶ DGAlgebra.Path.algebra R (SquareZero.algebra A N) :=
  DGAlgebra.RelativeHomotopyPullback.path R _ _ _

def relativeComparison : relativeModel N a ⟶ model N a :=
  DGAlgebra.RelativeHomotopyPullback.comparison R _ _ _

lemma projection_surjective (n : ℤ) :
    Function.Surjective ((SquareZero.projection A N).hom.f n) := by
  have : Epi (SquareZero.projection A N).hom := by
    change Epi (biprod.fst : A.X ⊞ N.X ⟶ A.X)
    infer_instance
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

lemma relativeComparison_quasiIso
    (hq : ∀ n : ℤ, Function.Surjective ((a ≫ SquareZero.projection A N).hom.f n)) :
    QuasiIso (relativeComparison N a).hom :=
  DGAlgebra.RelativeHomotopyPullback.comparison_quasiIso R _ _ _ (projection_surjective N) hq

lemma relativeComparison_left : relativeComparison N a ≫
    DGAlgebra.HomotopyPullbackModel.left R a (SquareZero.zeroSection A N) = relativeLeft N a :=
  DGAlgebra.RelativeHomotopyPullback.comparison_left R _ _ _

lemma relativeComparison_right : relativeComparison N a ≫
    DGAlgebra.HomotopyPullbackModel.right R a (SquareZero.zeroSection A N) = relativeRight N a :=
  DGAlgebra.RelativeHomotopyPullback.comparison_right R _ _ _

lemma relativeComparison_path : relativeComparison N a ≫
    DGAlgebra.HomotopyPullbackModel.path R a (SquareZero.zeroSection A N) = relativePath N a :=
  DGAlgebra.RelativeHomotopyPullback.comparison_path R _ _ _

lemma relativeRight_eq : relativeRight N a = relativeLeft N a ≫ a ≫ SquareZero.projection A N := by
  have h := DGAlgebra.RelativeHomotopyPullback.right_base R
    (SquareZero.projection A N) a (SquareZero.zeroSection A N)
  simpa only [relativeRight, relativeLeft, relativeModel,
    Category.assoc, SquareZero.zeroSection_projection, Category.comp_id] using h

lemma relativePath_base : relativePath N a ≫ DGAlgebra.Path.map R (SquareZero.projection A N) =
    relativeLeft N a ≫ a ≫ SquareZero.projection A N ≫ DGAlgebra.Path.diagonal R A :=
  DGAlgebra.RelativeHomotopyPullback.path_base R _ _ _

def relativeWitness : SquareZero.RelativeWitness
    (relativeLeft N a ≫ a ≫ SquareZero.projection A N) N
    (relativeLeft N a ≫ a) (relativeRight N a ≫ SquareZero.zeroSection A N) where
  hom := relativePath N a
  source_eq := DGAlgebra.RelativeHomotopyPullback.path_source R _ _ _
  target_eq := DGAlgebra.RelativeHomotopyPullback.path_target R _ _ _
  projection_eq := relativePath_base N a

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
