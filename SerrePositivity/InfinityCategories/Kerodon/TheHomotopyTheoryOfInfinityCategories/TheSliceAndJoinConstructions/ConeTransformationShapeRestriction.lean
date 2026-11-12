module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SourceConstantShapeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeCylinderShapeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeTransformationPointAt

/-!
概要：native な錐の元の標準変換は、図式の形状制限を厳密に保つ。
方針：指定頂点への等式を残して円柱を比較し、円柱表示の単射性を使う。
規約：図式・頂点を選び直さず、全変換空間の実際の制限射を使う。
使われ方：実切断の制限と錐の切断写像を全 fiber 上で比較する入口。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 同じ形状制限で得た錐の標準変換は、元の標準変換の実際の制限。 -/
lemma coneTransformationPointAt_shapeRestriction {A K X : SSet.{u}}
    (i : A ⟶ K) (F : K ⟶ X) (c : JoinCone F) (d : JoinCone (i ≫ F))
    (hd : d.val = joinMap (𝟙 (Δ[0] : SSet.{u})) i ≫ c.val)
    (z : X _⦋0⦌) (hc : c.vertex = z) (hz : d.vertex = z) :
    (sourceConstantShapeRestriction i F z).app (Opposite.op ⦋0⦌)
      (coneTransformationPointAt c z hc) = coneTransformationPointAt d z hz := by
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_comp]
  apply sourceConstantTransformationPrism_injective
  rw [sourceConstantShapeRestriction_prism, coneTransformationPointAt_prism,
    coneTransformationPointAt_prism, hd, whiskerRight_fst_assoc]
  rw [← Category.assoc (i ▷ (Δ[1] : SSet.{u})), coneCylinderMap_naturality]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
