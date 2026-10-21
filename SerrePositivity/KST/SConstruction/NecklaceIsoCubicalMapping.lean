module
public import SerrePositivity.KST.SConstruction.NecklaceInIsoTerminal
public import SerrePositivity.KST.SConstruction.NecklaceCubicalMapping
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # 元の necklace 全体の cubical mapping object の回収
概要：necklace と同型な入力の両端間の mapping object は、元の表現可能立方体と同型。
方針：元の全体が添字圏の終対象であることを、元の全 necklace の余極限に適用する。
規約：元の生成射と全可換三角形を回収。使われ方：標準単体上の Λ の Hom 計算。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Simplicial SSet

/-- 元の全体の生成射は、元の全図式の余極限から得る実同型。 -/
instance necklaceInOfIso_cell_isIso (U : Necklace.{u}) {K : SSet.{u}}
    (e : U.down.carrier ≅ K) : IsIso (necklaceCubicalCell (necklaceInOfIso U e)) :=
  isIso_ι_of_isTerminal (necklaceInOfIso_isTerminal U e)
    (necklaceCubicalDiagram K (e.hom.app _ U.down.firstVertex) (e.hom.app _ U.down.lastVertex))

/-- 同じ両端間の元の mapping object を、元の表現可能立方体で回収する実同型。 -/
def necklaceIsoCubicalMappingIso (U : Necklace.{u}) {K : SSet.{u}} (e : U.down.carrier ≅ K) :
    necklaceCubicalSet.obj U ≅
      necklaceCubicalMapping K
        (e.hom.app _ U.down.firstVertex) (e.hom.app _ U.down.lastVertex) :=
  @asIso CubicalSet.{u} _ _ _ (necklaceCubicalCell (necklaceInOfIso U e))
    (necklaceInOfIso_cell_isIso U e)

/-- 元の比較同型の正方向は、元の全体の生成射そのもの。 -/
lemma necklaceIsoCubicalMappingIso_hom (U : Necklace.{u}) {K : SSet.{u}}
    (e : U.down.carrier ≅ K) :
    (necklaceIsoCubicalMappingIso U e).hom = necklaceCubicalCell (necklaceInOfIso U e) := rfl

/-- 元の全生成射は、全体への元の可換三角形を比較同型に合成すると回収できる。 -/
lemma necklaceIsoCubicalMappingIso_cell (U : Necklace.{u}) {K : SSet.{u}}
    (e : U.down.carrier ≅ K)
    (T : NecklaceIn K (e.hom.app _ U.down.firstVertex) (e.hom.app _ U.down.lastVertex)) :
    necklaceCubicalSet.map (necklaceInToOfIso U e T).necklaceHom ≫
        (necklaceIsoCubicalMappingIso U e).hom = necklaceCubicalCell T :=
  necklaceCubicalCell_relation (necklaceInToOfIso U e T)

/-- 元の比較の逆方向は、全ての生成射で元の具体的立方体への射を回収する。 -/
lemma necklaceIsoCubicalMappingIso_cell_inv (U : Necklace.{u}) {K : SSet.{u}}
    (e : U.down.carrier ≅ K)
    (T : NecklaceIn K (e.hom.app _ U.down.firstVertex) (e.hom.app _ U.down.lastVertex)) :
    necklaceCubicalCell T ≫ (necklaceIsoCubicalMappingIso U e).inv =
      necklaceCubicalSet.map (necklaceInToOfIso U e T).necklaceHom := by
  have h := necklaceIsoCubicalMappingIso_cell U e T
  exact (congrArg (fun f => f ≫ (necklaceIsoCubicalMappingIso U e).inv) h.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f => necklaceCubicalSet.map (necklaceInToOfIso U e T).necklaceHom ≫ f)
        (necklaceIsoCubicalMappingIso U e).hom_inv_id).trans (Category.comp_id _)))

end SerrePositivity.KST.SConstruction
