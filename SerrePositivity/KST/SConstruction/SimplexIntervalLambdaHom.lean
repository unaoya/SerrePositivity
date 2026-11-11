module
public import SerrePositivity.KST.SConstruction.SimplexIntervalCubicalMapping
public import SerrePositivity.KST.SConstruction.CubicalLambdaComonoids

/-! # 標準単体の任意区間の Λ の Serre Hom
概要：元の a≤b の間の Λ の Hom 複体を、元の (b−a−1) 次元の Serre 鎖立方体で回収する。
方針：元の区間の cubical 同型に、元の鎖と余モノイド値関手を適用する。
規約：同じ順射と元の対角・増大を保持。使われ方：native HA 単体との比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
open scoped ComonObj
variable (A : Type u) [CommRing A]

/-- 元の任意区間の Λ の Hom 複体と、元の Serre 鎖立方体の実同型。 -/
def simplexIntervalLambdaHomIso {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    (serreConcreteCubeComplexFunctor A).obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1)) ≅
      homObject A (CubicalLambda A (Δ[n] : SSet.{u}))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) :=
  (cubicalSerreChainsCubeIso A).app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1)) ≪≫
    (cubicalSerreChains A).mapIso (simplexIntervalCubicalMappingIso a b hab)

/-- 元の任意区間の同じ比較を、Serre 余モノイドの実同型として読む。 -/
def simplexIntervalLambdaHomComonoidIso {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    (serreConcreteCubeFunctor A).obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1)) ≅
      cubicalLambdaHomComonoid A (Δ[n] : SSet.{u})
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) :=
  (cubicalSerreComonoidCubeIso A).app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1)) ≪≫
    (cubicalSerreComonoidFunctor A).mapIso (simplexIntervalCubicalMappingIso a b hab)

/-- 元の余モノイド比較の underlying 同型は、元の同じ Hom 比較そのもの。 -/
lemma simplexIntervalLambdaHomComonoidIso_forget {n : ℕ}
    (a b : Fin (n + 1)) (hab : a ≤ b) :
    (Comon.forget (Complex A)).mapIso (simplexIntervalLambdaHomComonoidIso A a b hab) =
      simplexIntervalLambdaHomIso A a b hab := by
  apply Iso.ext
  rfl

/-- 元の余モノイド比較の underlying 順射は、元の同じ Hom 比較の順射そのもの。 -/
lemma simplexIntervalLambdaHomComonoidIso_hom {n : ℕ}
    (a b : Fin (n + 1)) (hab : a ≤ b) :
    (simplexIntervalLambdaHomComonoidIso A a b hab).hom.hom =
      (simplexIntervalLambdaHomIso A a b hab).hom := rfl

/-- 元の全区間の Hom 比較は、元の Serre 対角を保つ。 -/
lemma simplexIntervalLambdaHomIso_diagonal {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    (simplexIntervalLambdaHomIso A a b hab).hom ≫
        Δ[(cubicalLambdaHomComonoid A (Δ[n] : SSet.{u})
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)).X] =
      Δ[((serreConcreteCubeFunctor A).obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1))).X] ≫
        ((simplexIntervalLambdaHomIso A a b hab).hom ⊗ₘ
          (simplexIntervalLambdaHomIso A a b hab).hom) :=
  (simplexIntervalLambdaHomComonoidIso A a b hab).hom.isComonHom_hom.hom_comul

/-- 元の全区間の Hom 比較は、元の Serre 増大を保つ。 -/
lemma simplexIntervalLambdaHomIso_augmentation {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    (simplexIntervalLambdaHomIso A a b hab).hom ≫
        ε[(cubicalLambdaHomComonoid A (Δ[n] : SSet.{u})
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)).X] =
      ε[((serreConcreteCubeFunctor A).obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1))).X] :=
  (simplexIntervalLambdaHomComonoidIso A a b hab).hom.isComonHom_hom.hom_counit

end SerrePositivity.KST.SConstruction
