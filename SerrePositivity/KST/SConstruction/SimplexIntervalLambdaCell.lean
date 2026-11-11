module
public import SerrePositivity.KST.SConstruction.SimplexIntervalLambdaHom
public import SerrePositivity.KST.SConstruction.NecklaceLambdaComposition
public import SerrePositivity.KST.SConstruction.SimplexIntervalComposeOneFace
public import SerrePositivity.KST.SConstruction.SerreCubeChainFace

/-! # 元の全区間 Hom 比較と実 necklace Serre 生成射
概要：元の区間 Hom 同型の順射と、同じ区間 bead の Serre 生成射を照合する。
方針：元の表現可能 cube 比較の自然性と、全 necklace 表示関係を使う。
規約：元の両端・次元移送を保持。使われ方：実二区間の合成と HA 復元の合成の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の任意区間 Hom 同型の順射は、同じ次元移送と元の bead の Serre 生成射。 -/
lemma simplexIntervalLambdaHomIso_cell {N : ℕ} (a b : Fin (N + 1)) (hab : a ≤ b) :
    (simplexIntervalLambdaHomIso A a b hab).hom =
      eqToHom (congrArg (serreCubeComplex A)
        (necklaceBead_dimension.{u} (b.val - a.val)).symm) ≫
          necklaceLambdaCell A (necklaceInSimplexInterval.{u} a b hab) := by
  let f := (concreteCubeDimensionIso
    (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1))
    (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} (b.val - a.val)).down.dimension)
    (necklaceBead_dimension.{u} (b.val - a.val)).symm).hom
  have h := (cubicalSerreChainsCubeIso A).hom.naturality f
  have hd : (serreConcreteCubeComplexFunctor A).map f = eqToHom
      (congrArg (serreCubeComplex A)
        (necklaceBead_dimension.{u} (b.val - a.val)).symm) := by
    exact serreCubeComplexMap_dimension_inv A (necklaceBead_dimension.{u} _)
  have h₁ : (simplexIntervalLambdaHomIso A a b hab).hom =
      (cubicalSerreChainsCubeIso A).hom.app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (b.val - a.val - 1)) ≫
        ((cubicalSerreChains A).map (cubicalYoneda.map f) ≫
          (cubicalSerreChains A).map
            (necklaceCubicalCell (necklaceInSimplexInterval.{u} a b hab))) :=
    congrArg (fun g => (cubicalSerreChainsCubeIso A).hom.app _ ≫ g)
      ((cubicalSerreChains A).map_comp _ _)
  exact h₁.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (cubicalSerreChains A).map
      (necklaceCubicalCell (necklaceInSimplexInterval.{u} a b hab))) h.symm).trans
        ((congrArg (fun g => (g ≫ (cubicalSerreChainsCubeIso A).hom.app _) ≫
          (cubicalSerreChains A).map
            (necklaceCubicalCell (necklaceInSimplexInterval.{u} a b hab))) hd).trans
              (Category.assoc _ _ _))))

/-- 元の二区間の連結生成射は、元の実合成 cube と全区間生成射の合成。 -/
lemma simplexIntervalLambdaCell_wedge {N : ℕ} (a b c : Fin (N + 1))
    (hab : a ≤ b) (hbc : b ≤ c) :
    necklaceLambdaCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge (necklaceInSimplexInterval.{u} a b hab)
      (necklaceInSimplexInterval b c hbc)) =
        (serreConcreteCubeComplexFunctor A).map
          (necklaceConcreteCubeMap (simplexIntervalComposeBeadHom.{u} a b c hab hbc)) ≫
            necklaceLambdaCell A (necklaceInSimplexInterval a c (hab.trans hbc)) :=
  (necklaceLambdaCell_relation A (necklaceInToSimplexInterval a c (hab.trans hbc)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge (necklaceInSimplexInterval a b hab)
      (necklaceInSimplexInterval b c hbc)))).symm

end SerrePositivity.KST.SConstruction
