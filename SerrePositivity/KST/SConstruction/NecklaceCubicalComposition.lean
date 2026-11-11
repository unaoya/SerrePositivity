module
public import SerrePositivity.KST.SConstruction.CubicalDayBicolimit
public import SerrePositivity.KST.SConstruction.NecklaceCubicalComposeCell

/-! # 元の necklace mapping object 上の cubical 合成
概要：元の両 mapping object の Day tensor から wedge による合成を構成する。
方針：全生成射の合成と全表示関係を、両変数の余極限の普遍性で降ろす。
規約：元の生成射を厳密に回収する。使われ方：cubical rigidification の合成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits Simplicial SSet

variable (K : SSet.{u}) (x y z : K _⦋0⦌)

/-- 元の二つの全 necklace 図式上で、同じ wedge 合成が定める余錐。 -/
def necklaceCubicalComposeCocone : Cocone
    (cubicalDayPairDiagram (necklaceCubicalDiagram K x y) (necklaceCubicalDiagram K y z)) where
  pt := necklaceCubicalMapping K x z
  ι :=
    { app := fun p => necklaceCubicalComposeCell p.1 p.2
      naturality := by
        intro p q f
        change (cubicalDayTensorMap
            (necklaceCubicalSet.map f.1.necklaceHom) (𝟙 _) ≫
          cubicalDayTensorMap (𝟙 _) (necklaceCubicalSet.map f.2.necklaceHom)) ≫
            necklaceCubicalComposeCell q.1 q.2 = necklaceCubicalComposeCell p.1 p.2 ≫ 𝟙 _
        rw [← cubicalDayTensorMap_comp, Category.comp_id, Category.id_comp, Category.comp_id]
        exact necklaceCubicalComposeCell_relation f.1 f.2 }

/-- 元の全 necklace の mapping object 上の Day tensor 値の合成。 -/
def necklaceCubicalCompose :
    cubicalDayTensor (necklaceCubicalMapping K x y) (necklaceCubicalMapping K y z) ⟶
      necklaceCubicalMapping K x z :=
  (cubicalDayPairIsColimit (necklaceCubicalDiagram K x y)
    (necklaceCubicalDiagram K y z)).desc (necklaceCubicalComposeCocone K x y z)

/-- 全ての元の両生成射について、合成は指定した wedge の生成射を回収する。 -/
lemma necklaceCubicalCompose_cell (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z) :
    cubicalDayTensorMap (necklaceCubicalCell T) (necklaceCubicalCell U) ≫
      necklaceCubicalCompose K x y z = necklaceCubicalComposeCell T U := by
  have h := (cubicalDayPairIsColimit (necklaceCubicalDiagram K x y)
    (necklaceCubicalDiagram K y z)).fac (necklaceCubicalComposeCocone K x y z) (T, U)
  exact (congrArg (fun a => a ≫ necklaceCubicalCompose K x y z)
    (cubicalDayPairCocone_ι (necklaceCubicalDiagram K x y)
      (necklaceCubicalDiagram K y z) T U).symm).trans h

/-- 元の全ての両生成射の Day tensor で、同じ source からの射を判定する。 -/
lemma necklaceCubicalTensor_hom_ext {M : CubicalSet.{u}}
    {f g : cubicalDayTensor (necklaceCubicalMapping K x y)
      (necklaceCubicalMapping K y z) ⟶ M}
    (h : ∀ (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K y z),
      cubicalDayTensorMap (necklaceCubicalCell T) (necklaceCubicalCell U) ≫ f =
        cubicalDayTensorMap (necklaceCubicalCell T) (necklaceCubicalCell U) ≫ g) : f = g := by
  apply (cubicalDayPairIsColimit (necklaceCubicalDiagram K x y)
    (necklaceCubicalDiagram K y z)).hom_ext
  intro p
  exact (congrArg (fun a => a ≫ f) (cubicalDayPairCocone_ι _ _ p.1 p.2)).trans
    ((h p.1 p.2).trans
      (congrArg (fun a => a ≫ g) (cubicalDayPairCocone_ι _ _ p.1 p.2)).symm)

end SerrePositivity.KST.SConstruction
