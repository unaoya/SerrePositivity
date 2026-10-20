module
public import SerrePositivity.KST.SConstruction.PointedFamilyConstantComposition

/-! # 固定した段頂点との全族の同じ豊穣合成
概要：固定した Hom 頂点による全 Hom 写像を、元の全族との射対の合成として回収する。
方針：定数族と恒等射の射対へ同じ族を前合成する。
規約：元の全パラメータの実写像の等式を用いる。
使われ方：元の単一射補正の後続部分を、同じ BF 段頂点の前合成へ写す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance fixedVertexPointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 固定した第一頂点との全 Hom 合成へ前合成すると、同じ全族との合成を回収する。 -/
lemma pointedFixedLeftVertexComposition_apply {U : SSet.{u}}
    {A B C : PointedSimplicialSet.{u}} (v : (PointedObject.basedHom A B).right _⦋0⦌)
    (b : U ⟶ (PointedObject.basedHom B C).right) :
    b ≫ (lift (SSet.const v) (𝟙 _) ≫ eComp SSet A B C) =
      lift (SSet.const v) b ≫ eComp SSet A B C := by
  rw [← Category.assoc, comp_lift, SSet.comp_const, Category.comp_id]

end SerrePositivity.KST.SConstruction
