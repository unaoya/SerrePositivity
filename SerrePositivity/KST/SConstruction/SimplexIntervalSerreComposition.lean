module
public import SerrePositivity.KST.SConstruction.SimplexIntervalLambdaCell

/-! # 元の二区間の実 Serre 合成と共有頂点の鎖一面
概要：元の区間 bead の合成を、同じ共有頂点の実 Serre 一面に分解する。
方針：実 cube の一面判定へ元の鎖関手を適用し、全 necklace 表示関係と合成する。
規約：元の tensor 順・端点・右端座標を保持。使われ方：native HA 逆写像の合成保存。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の厳密二区間の実合成 Serre 射は、共有頂点の同じ鎖一面と次元移送。 -/
lemma simplexIntervalCompose_serre_factor {N : ℕ} (a b c : Fin (N + 1))
    (hab : a < b) (hbc : b < c) :
    (serreConcreteCubeComplexFunctor A).map
        (necklaceConcreteCubeMap (simplexIntervalComposeBeadHom.{u} a b c hab.le hbc.le)) =
      (serreCubeFace A true
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} (b.val - a.val))
          (necklaceBead (c.val - b.val))).down.dimension
        (simplexIntervalComposeCoordinate.{u} a b c hab hbc)).hom ≫
          eqToHom (congrArg (serreCubeComplex A)
            (simplexIntervalCompose_codimension.{u} a b c hab hbc).symm) := by
  let T := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} (b.val - a.val))
    (necklaceBead (c.val - b.val))
  let e := concreteCubeDimensionIso
    (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (necklaceBead.{u} (c.val - a.val)).down.dimension)
    (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (T.down.dimension + 1))
    (simplexIntervalCompose_codimension.{u} a b c hab hbc)
  have hf := (Iso.eq_comp_inv e).mpr (simplexIntervalCompose_cube_one_face.{u, u} a b c hab hbc)
  have h := congrArg ((serreConcreteCubeComplexFunctor A).map) hf
  have hd := serreCubeComplexMap_dimension_inv A
    (simplexIntervalCompose_codimension.{u} a b c hab hbc)
  have hface : (serreConcreteCubeComplexFunctor A).map
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace true T.down.dimension
        (simplexIntervalComposeCoordinate.{u} a b c hab hbc)) =
      (serreCubeFace A true T.down.dimension
        (simplexIntervalComposeCoordinate.{u} a b c hab hbc)).hom :=
    congrArg ((Comon.forget (Complex A)).map)
      (serreConcreteCubeFunctor_face A true T.down.dimension
        (simplexIntervalComposeCoordinate.{u} a b c hab hbc))
  exact h.trans (((serreConcreteCubeComplexFunctor A).map_comp _ _).trans
    ((congrArg (fun f => f ≫ (serreConcreteCubeComplexFunctor A).map e.inv) hface).trans
      (congrArg (fun f => (serreCubeFace A true T.down.dimension
        (simplexIntervalComposeCoordinate.{u} a b c hab hbc)).hom ≫ f) hd)))

/-- 元の二区間の実豊穣合成は、同じ連結 cube と全区間への元の射で回収される。 -/
lemma simplexIntervalLambdaCell_composition {N : ℕ} (a b c : Fin (N + 1))
    (hab : a ≤ b) (hbc : b ≤ c) :
    (serreCubeTensorIso A (necklaceBead.{u} (b.val - a.val)).down.dimension
        (necklaceBead.{u} (c.val - b.val)).down.dimension).hom.hom ≫
      (necklaceLambdaCell A (necklaceInSimplexInterval.{u} a b hab) ⊗ₘ
        necklaceLambdaCell A (necklaceInSimplexInterval b c hbc)) ≫
      eComp (Complex A) (C := CubicalLambda A (Δ[N] : SSet.{u}))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) =
      (serreConcreteCubeComplexFunctor A).map
        (necklaceCubeTensorIso (necklaceBead.{u} (b.val - a.val))
          (necklaceBead (c.val - b.val))).hom ≫
        (serreConcreteCubeComplexFunctor A).map
          (necklaceConcreteCubeMap (simplexIntervalComposeBeadHom.{u} a b c hab hbc)) ≫
          necklaceLambdaCell A (necklaceInSimplexInterval a c (hab.trans hbc)) :=
  (necklaceLambdaCell_composition A (necklaceInSimplexInterval.{u} a b hab)
    (necklaceInSimplexInterval b c hbc)).trans
      (congrArg (fun f => (serreConcreteCubeComplexFunctor A).map
        (necklaceCubeTensorIso (necklaceBead.{u} (b.val - a.val))
          (necklaceBead (c.val - b.val))).hom ≫ f)
        (simplexIntervalLambdaCell_wedge A a b c hab hbc))

/-- 元の厳密二区間の実豊穣合成は、同じ共有頂点の実鎖一面を経由する。 -/
lemma simplexIntervalLambdaCell_composition_one_face {N : ℕ} (a b c : Fin (N + 1))
    (hab : a < b) (hbc : b < c) :
    (serreCubeTensorIso A (necklaceBead.{u} (b.val - a.val)).down.dimension
        (necklaceBead.{u} (c.val - b.val)).down.dimension).hom.hom ≫
      (necklaceLambdaCell A (necklaceInSimplexInterval.{u} a b hab.le) ⊗ₘ
        necklaceLambdaCell A (necklaceInSimplexInterval b c hbc.le)) ≫
      eComp (Complex A) (C := CubicalLambda A (Δ[N] : SSet.{u}))
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) =
      (serreConcreteCubeComplexFunctor A).map
        (necklaceCubeTensorIso (necklaceBead.{u} (b.val - a.val))
          (necklaceBead (c.val - b.val))).hom ≫
        (serreCubeFace A true
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (necklaceBead.{u} (b.val - a.val))
            (necklaceBead (c.val - b.val))).down.dimension
          (simplexIntervalComposeCoordinate.{u} a b c hab hbc)).hom ≫
        eqToHom (congrArg (serreCubeComplex A)
          (simplexIntervalCompose_codimension.{u} a b c hab hbc).symm) ≫
          necklaceLambdaCell A (necklaceInSimplexInterval a c (hab.le.trans hbc.le)) := by
  have h := simplexIntervalCompose_serre_factor A a b c hab hbc
  have h₁ := congrArg (fun f => f ≫
    necklaceLambdaCell A (necklaceInSimplexInterval.{u} a c (hab.le.trans hbc.le))) h
  exact (simplexIntervalLambdaCell_composition A a b c hab.le hbc.le).trans
    (congrArg (fun f => (serreConcreteCubeComplexFunctor A).map
      (necklaceCubeTensorIso (necklaceBead.{u} (b.val - a.val))
        (necklaceBead (c.val - b.val))).hom ≫ f)
      (h₁.trans (Category.assoc _ _ _)))

end SerrePositivity.KST.SConstruction
