module
public import SerrePositivity.KST.SConstruction.NecklaceCubeTensorComparison
public import SerrePositivity.KST.SConstruction.CubicalDayRepresentableNaturality

/-! # 元の necklace の wedge と表現可能 Day tensor の比較
概要：全 necklace 射に自然な、元の cubical 生成射を保つ Day tensor 同型を作る。
方針：元の表現可能 Day 比較と具体的 cube tensor 比較を合成する。
規約：元の全 cell の作用を回収。使われ方：mapping object の余極限上の合成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite

/-- 元の左右の表現可能 cubical set の Day tensor と、元の wedge の cubical set の同型。 -/
def necklaceCubicalTensorIso (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    cubicalDayTensor (necklaceCubicalSet.obj T) (necklaceCubicalSet.obj U) ≅
      necklaceCubicalSet.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T U) :=
  cubicalDayCubeIso (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk T.down.dimension) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk U.down.dimension) ≪≫
    cubicalYoneda.mapIso (necklaceCubeTensorIso T U)

/-- 元の全 necklace 射で、同じ表現可能 Day 比較は厳密に可換。 -/
lemma necklaceCubicalTensorIso_naturality {T T' U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}}
    (f : T ⟶ T') (g : U ⟶ U') :
    cubicalDayTensorMap (necklaceCubicalSet.map f) (necklaceCubicalSet.map g) ≫
        (necklaceCubicalTensorIso T' U').hom =
      (necklaceCubicalTensorIso T U).hom ≫ necklaceCubicalSet.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g) := by
  change cubicalDayTensorMap (cubicalYoneda.map (necklaceConcreteCubeMap f))
      (cubicalYoneda.map (necklaceConcreteCubeMap g)) ≫
        (cubicalDayCubeProjection _ _ ≫ cubicalYoneda.map (necklaceCubeTensorIso T' U').hom) =
    (cubicalDayCubeProjection _ _ ≫ cubicalYoneda.map (necklaceCubeTensorIso T U).hom) ≫
      cubicalYoneda.map (necklaceConcreteCubeMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g))
  have h := congrArg (fun e => cubicalYoneda.{u}.map e)
    (necklaceCubeTensorIso_naturality f g)
  have hs : cubicalYoneda.{u}.map
        (concreteCubeTensorMap (necklaceConcreteCubeMap f) (necklaceConcreteCubeMap g)) ≫
      cubicalYoneda.map (necklaceCubeTensorIso T' U').hom =
    cubicalYoneda.map (necklaceCubeTensorIso T U).hom ≫
      cubicalYoneda.map (necklaceConcreteCubeMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g)) :=
    (cubicalYoneda.map_comp _ _).symm.trans (h.trans (cubicalYoneda.map_comp _ _))
  rw [← Category.assoc, cubicalDayCubeProjection_naturality, Category.assoc]
  exact (congrArg (fun e => cubicalDayCubeProjection
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk T.down.dimension) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk U.down.dimension) ≫ e) hs).trans
      (Category.assoc _ _ _).symm

/-- 全元の necklace 射に自然な、表現可能 Day tensor 比較の二変数自然同型。 -/
def necklaceCubicalTensorNatIso :
    necklaceCubicalSet.{u}.prod necklaceCubicalSet.{u} ⋙ cubicalDayTensorFunctor ≅
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeFunctor ⋙ necklaceCubicalSet :=
  NatIso.ofComponents (fun p => necklaceCubicalTensorIso p.1 p.2)
    (fun f => necklaceCubicalTensorIso_naturality f.1 f.2)

/-- 元の全連結 cell で、比較は左右の元の射と元の次元同型の合成を回収する。 -/
lemma necklaceCubicalTensorIso_cell (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) (a b : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (p : a ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk T.down.dimension) (q : b ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk U.down.dimension) :
    (necklaceCubicalTensorIso T U).hom.app (op (concreteCubeTensorObj a b))
        (cubicalDayTensorCell a b (ULift.up p) (ULift.up q)) =
      ULift.up (concreteCubeTensorMap p q ≫ (necklaceCubeTensorIso T U).hom) := by
  change ULift.up (((cubicalDayCubeProjection _ _).app (op (concreteCubeTensorObj a b))
    (cubicalDayTensorCell a b (ULift.up p) (ULift.up q))).down ≫
      (necklaceCubeTensorIso T U).hom) = _
  rw [cubicalDayCubeProjection_cell]

end SerrePositivity.KST.SConstruction
