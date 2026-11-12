module
public import SerrePositivity.KST.SConstruction.SimplexBeadCubicalMapping
public import SerrePositivity.KST.SConstruction.CubicalLambdaComonoids

/-! # 元の標準単体の両端間の Λ の Hom 複体
概要：標準 n 単体の元の始端と終端の間の Hom を、元の Serre 鎖立方体として回収する。
方針：元の cubical 同型に Serre 鎖と余モノイド値関手を適用し、同じ underlying 射を照合する。
規約：n=0 と全対角・増大を保持。使われ方：native dg nerve の部分集合成分との比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
open scoped ComonObj
variable (A : Type u) [CommRing A]

/-- 元の標準単体の両端間の Λ の Hom は、元の (n−1) 次元の Serre 鎖立方体と同型。 -/
def simplexBeadLambdaHomIso (n : ℕ) :
    (serreConcreteCubeComplexFunctor A).obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n - 1)) ≅
      homObject A (CubicalLambda A (Δ[n] : SSet.{u}))
        (simplexBeadFirstVertex n) (simplexBeadLastVertex n) :=
  (cubicalSerreChainsCubeIso A).app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n - 1)) ≪≫
    (cubicalSerreChains A).mapIso (simplexBeadCubicalMappingIso n)

/-- 同じ Hom の比較を、元の対角・増大を保つ Serre 余モノイドの実同型として読む。 -/
def simplexBeadLambdaHomComonoidIso (n : ℕ) :
    (serreConcreteCubeFunctor A).obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n - 1)) ≅
      cubicalLambdaHomComonoid A (Δ[n] : SSet.{u})
        (simplexBeadFirstVertex n) (simplexBeadLastVertex n) :=
  (cubicalSerreComonoidCubeIso A).app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n - 1)) ≪≫
    (cubicalSerreComonoidFunctor A).mapIso (simplexBeadCubicalMappingIso n)

/-- 元の余モノイド比較の underlying 同型は、同じ Hom 複体の比較そのもの。 -/
lemma simplexBeadLambdaHomComonoidIso_forget (n : ℕ) :
    (Comon.forget (Complex A)).mapIso (simplexBeadLambdaHomComonoidIso A n) =
      simplexBeadLambdaHomIso A n := by
  apply Iso.ext
  rfl

/-- 元の余モノイド比較の underlying 順射は、元の Hom 複体の比較の順射そのもの。 -/
lemma simplexBeadLambdaHomComonoidIso_hom (n : ℕ) :
    (simplexBeadLambdaHomComonoidIso A n).hom.hom = (simplexBeadLambdaHomIso A n).hom := rfl

/-- 元の Hom 比較は元の全 Serre 対角を保つ。 -/
lemma simplexBeadLambdaHomIso_diagonal (n : ℕ) :
    (simplexBeadLambdaHomIso A n).hom ≫
        Δ[(cubicalLambdaHomComonoid A (Δ[n] : SSet.{u})
          (simplexBeadFirstVertex n) (simplexBeadLastVertex n)).X] =
      Δ[((serreConcreteCubeFunctor A).obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n - 1))).X] ≫
        ((simplexBeadLambdaHomIso A n).hom ⊗ₘ
          (simplexBeadLambdaHomIso A n).hom) :=
  (simplexBeadLambdaHomComonoidIso A n).hom.isComonHom_hom.hom_comul

/-- 元の Hom 比較は元の Serre 増大を保つ。 -/
lemma simplexBeadLambdaHomIso_augmentation (n : ℕ) :
    (simplexBeadLambdaHomIso A n).hom ≫
        ε[(cubicalLambdaHomComonoid A (Δ[n] : SSet.{u})
          (simplexBeadFirstVertex n) (simplexBeadLastVertex n)).X] =
      ε[((serreConcreteCubeFunctor A).obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n - 1))).X] :=
  (simplexBeadLambdaHomComonoidIso A n).hom.isComonHom_hom.hom_counit

end SerrePositivity.KST.SConstruction
