module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSimplicialConvolution
public import Mathlib.CategoryTheory.Limits.Presheaf

/-!
概要：実 AW 畳み込みの、全標準単体上の互換な射に対する普遍性。
方針：標準単体の正本の稠密余極限を、反変極限保存で実代数の極限へ送る。
規約：元の単体・元の代数射を保持し、Kan 性を入力しない。
使われ方：実ホーンの全境界データを一つの制限代数への射へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) (K : SSet.{0})

abbrev simplexConvolutionIndex := CostructuredArrow SSet.stdSimplex.{0} K

def simplexConvolutionDensityDiagram : (simplexConvolutionIndex K)ᵒᵖ ⥤ Mon (Complex R) :=
  (CostructuredArrow.proj SSet.stdSimplex K ⋙ SSet.stdSimplex).op ⋙ simplicialConvolution R B

def simplexConvolutionDensityCone : Cone (simplexConvolutionDensityDiagram R B K) :=
  (simplicialConvolution R B).mapCone (Presheaf.tautologicalCocone' K).op

def simplexConvolutionDensityCone_isLimit : IsLimit (simplexConvolutionDensityCone R B K) :=
  isLimitOfPreserves (simplicialConvolution R B) (Presheaf.isColimitTautologicalCocone' K).op

variable {A : Mon (Complex R)}
  (a : (Functor.const (simplexConvolutionIndex K)ᵒᵖ).obj A ⟶
    simplexConvolutionDensityDiagram R B K)

def simplexConvolutionDensityLift : A ⟶ (simplicialConvolution R B).obj (Opposite.op K) :=
  (simplexConvolutionDensityCone_isLimit R B K).lift ⟨A, a⟩

lemma simplexConvolutionDensityLift_fac (i : (simplexConvolutionIndex K)ᵒᵖ) :
    simplexConvolutionDensityLift R B K a ≫ (simplexConvolutionDensityCone R B K).π.app i =
      a.app i :=
  (simplexConvolutionDensityCone_isLimit R B K).fac ⟨A, a⟩ i

lemma simplexConvolutionDensityLift_unique (f : A ⟶ (simplicialConvolution R B).obj (Opposite.op K))
    (hf : ∀ i, f ≫ (simplexConvolutionDensityCone R B K).π.app i = a.app i) :
    f = simplexConvolutionDensityLift R B K a :=
  (simplexConvolutionDensityCone_isLimit R B K).uniq ⟨A, a⟩ f hf

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
