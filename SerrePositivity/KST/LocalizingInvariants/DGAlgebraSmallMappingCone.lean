module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSimplicialConvolutionDensity

/-!
概要：小さい単体集合からの実乗法的写像を、同じ AW 制限代数への射へ戻す。
方針：元の全単体の像を互換な代数錐へ束ね、実密度極限で貼り合わせる。
規約：宇宙の持ち上げを明示し、元の全単体・全境界の値を保持する。
使われ方：cell 源上の実ホーン充填と指定底の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} {K : SSet.{0}}
  (a : SSet.uliftFunctor.{u, 0}.obj K ⟶ multiplicativeMappingSimplices R A B)

set_option maxHeartbeats 800000 in -- 元の AW 単体と密度図式の全対象・全射を照合する。
def smallMultiplicativeMappingCone : Cone (simplexConvolutionDensityDiagram R B K) where
  pt := A
  π :=
    { app := fun i => a.app (op i.unop.left) ⟨SSet.yonedaEquiv.{0} i.unop.hom⟩
      naturality := by
        intro i j f
        change a.app (op j.unop.left) ⟨SSet.yonedaEquiv.{0} j.unop.hom⟩ =
          a.app (op i.unop.left) ⟨SSet.yonedaEquiv.{0} i.unop.hom⟩ ≫
            convolutionPrecompose R
              ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexCochainComonFunctor R).map f.unop.left) B
        have h := ConcreteCategory.congr_hom (a.naturality f.unop.left.op)
          (ULift.up.{u, 0} (SSet.yonedaEquiv.{0} i.unop.hom))
        change a.app (op j.unop.left)
            ⟨K.map f.unop.left.op (SSet.yonedaEquiv.{0} i.unop.hom)⟩ =
          a.app (op i.unop.left) ⟨SSet.yonedaEquiv.{0} i.unop.hom⟩ ≫
            convolutionPrecompose R
              ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexCochainComonFunctor R).map f.unop.left) B at h
        rw [SSet.yonedaEquiv_naturality, CostructuredArrow.w f.unop] at h
        exact h }

def smallMultiplicativeMappingTranspose : A ⟶ (simplicialConvolution R B).obj (op K) :=
  (simplexConvolutionDensityCone_isLimit R B K).lift (smallMultiplicativeMappingCone R a)

lemma smallMultiplicativeMappingTranspose_fac (i : (simplexConvolutionIndex K)ᵒᵖ) :
    smallMultiplicativeMappingTranspose R a ≫ (simplexConvolutionDensityCone R B K).π.app i =
      a.app (op i.unop.left) ⟨SSet.yonedaEquiv.{0} i.unop.hom⟩ :=
  (simplexConvolutionDensityCone_isLimit R B K).fac (smallMultiplicativeMappingCone R a) i

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
