module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanConeKanPathClass
public import SerrePositivity.InfinityCategories.F2.CoherentTotalVertexPathClass

/-!
概要：底固定円柱からの値の指定可換同型は既存 native 比較候補の指定可換同型に等しい。
方針：Kan 延長後の指定同型の等式を頂点表示へ移し、同じ合成の等式で両端を揃える。
規約：同型の存在でなく指定値の等式。使われ方：全空間模型と既存比較候補の path 接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)

/-- 概要：既存の値の可換同型は元の全空間円柱の延長の両端輸送そのもの。
方針：同じ全円柱の指定同型の端点だけを移す。
規約：既存の指定値を保持。使われ方：底固定代表との比較。 -/
lemma coherentCospanConeValuePathIso_eq_transport :
    coherentCospanConeValuePathIso F X Y Z C =
      functorIsoOfEq (coherentTotalVertexPathIso F Z
        (coherentCospanConeTotalPathHomotopy F X Y Z C))
        (coherentTotalVertexMap_comp F X Z _ _) (coherentTotalVertexMap_comp F Y Z _ _) := by
  symm
  exact functorIsoOfEq_of_homotopy_h_eq
    (coherentTotalVertexPathHomotopy F Z (coherentCospanConeTotalPathHomotopy F X Y Z C))
    (coherentCospanConeValuePathHomotopy F X Y Z C) _ _ rfl rfl _ _ rfl

/-- 概要：元の底固定円柱からの値の指定可換同型。
方針：同じ円柱の Kan 延長と元の合成式による端点輸送。
規約：元の底固定代表を使用。使われ方：全空間模型の元の path と値の比較。 -/
def coherentCospanConeRelativeValuePathIso :=
  functorIsoOfEq (coherentTotalVertexPathIso F Z
    (coherentCospanConeRelativePathHomotopy F X Y Z C))
    (coherentTotalVertexMap_comp F X Z _ _) (coherentTotalVertexMap_comp F Y Z _ _)

/-- 概要：底固定模型からの指定可換同型と既存比較候補の指定可換同型は厳密に等しい。
方針：単位上の類を Kan 延長後へ反映し、同じ頂点表示と端点輸送を使う。
規約：元の指定値の等式。使われ方：native 比較候補の弱同値性への接続。 -/
lemma coherentCospanConeRelativeValuePathIso_eq :
    coherentCospanConeRelativeValuePathIso F X Y Z C =
      coherentCospanConeValuePathIso F X Y Z C := by
  have h := coherentTotalVertexPathIso_eq_of_kan_iso F Z
    (coherentCospanConeRelativePathHomotopy F X Y Z C)
    (coherentCospanConeTotalPathHomotopy F X Y Z C)
    (coherentCospanConeRelativePathHomotopy_kan_iso F X Y Z C)
  rw [coherentCospanConeValuePathIso_eq_transport]
  unfold coherentCospanConeRelativeValuePathIso
  rw [h]

end SerrePositivity.InfinityCategories.F2
