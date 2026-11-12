module
public import SerrePositivity.KST.SConstruction.NecklaceCubicalTensorComparison
public import SerrePositivity.KST.SConstruction.NecklaceCubicalMapping
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInWedge

/-! # 元の二つの necklace 生成射の cubical 合成
概要：元の両生成射の Day tensor を、同じ K 内の wedge の生成射へ送る。
方針：元の tensor 比較と全可換三角形の表示関係を合成する。
規約：余極限全体の合成への降下は後続。使われ方：元の cubical 合成の生成射の指定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite Simplicial SSet

/-- 元の二つの necklace の Day tensor から、元の連結の生成射への合成。 -/
def necklaceCubicalComposeCell {K : SSet.{u}} {x y z : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    cubicalDayTensor (necklaceCubicalSet.obj T.necklace) (necklaceCubicalSet.obj U.necklace) ⟶
      necklaceCubicalMapping K x z :=
  (necklaceCubicalTensorIso T.necklace U.necklace).hom ≫
    necklaceCubicalCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U)

/-- 元の両生成射の合成は、全ての両側の可換三角形の表示関係を保つ。 -/
lemma necklaceCubicalComposeCell_relation {K : SSet.{u}} {x y z : K _⦋0⦌}
    {T T' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y} {U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z} (f : T ⟶ T') (g : U ⟶ U') :
    cubicalDayTensorMap (necklaceCubicalSet.map f.necklaceHom)
        (necklaceCubicalSet.map g.necklaceHom) ≫ necklaceCubicalComposeCell T' U' =
      necklaceCubicalComposeCell T U := by
  have h := necklaceCubicalTensorIso_naturality f.necklaceHom g.necklaceHom
  have hc := necklaceCubicalCell_relation (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedgeMap f g)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun e => e ≫ necklaceCubicalCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T' U')) h).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun e => (necklaceCubicalTensorIso T.necklace U.necklace).hom ≫ e) hc)))

/-- 元の全 cell 上で、生成射の合成は同じ元の具体的 tensor 射を回収する。 -/
lemma necklaceCubicalComposeCell_apply {K : SSet.{u}} {x y z : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) (a b : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (p : a ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk T.necklace.down.dimension)
    (q : b ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk U.necklace.down.dimension) :
    (necklaceCubicalComposeCell T U).app (op (concreteCubeTensorObj a b))
        (cubicalDayTensorCell a b (ULift.up p) (ULift.up q)) =
      (necklaceCubicalCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U)).app (op (concreteCubeTensorObj a b))
        (ULift.up (concreteCubeTensorMap p q ≫
          (necklaceCubeTensorIso T.necklace U.necklace).hom)) :=
  congrArg ((necklaceCubicalCell (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInWedge T U)).app _)
    (necklaceCubicalTensorIso_cell T.necklace U.necklace a b p q)

end SerrePositivity.KST.SConstruction
