module
public import SerrePositivity.KST.SConstruction.FixedBoundaryPullback

/-! # 元の指定点を固定する全単体パラメータ
概要：指定頂点を固定した全パラメータ族を構成し、全単体作用素の厳密な自然性を与える。
方針：定数な第一射影と恒等な第二射影を同じ積への射対にする。
規約：選択を含まず、元の全単体の像を保持する。
使われ方：元の各段 span 三角形を直通列点へ制限し、その全三辺を回収する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 元の指定頂点を固定し、任意の元の全パラメータだけを動かす実写像。 -/
def pointParameterMap {P : SSet.{u}} (v : P _⦋0⦌) (T : SSet.{u}) : T ⟶ P ⊗ T :=
  lift (SSet.const v) (𝟙 _)

/-- 元の全パラメータ写像に関して、同じ指定点を固定する四角形は厳密に可換。 -/
lemma pointParameterMap_naturality {P T U : SSet.{u}} (v : P _⦋0⦌) (f : T ⟶ U) :
    f ≫ pointParameterMap v U = pointParameterMap v T ≫ (P ◁ f) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [pointParameterMap, Category.assoc, lift_fst, lift_snd, whiskerLeft_fst,
      whiskerLeft_snd, SSet.comp_const, Category.comp_id, Category.id_comp, lift_snd_assoc]

/-- 元の全区間パラメータは、同じ一般の一点制限の区間の場合。 -/
lemma pointParameterMap_interval {P : SSet.{u}} (v : P _⦋0⦌) :
    pointParameterMap v (Δ[1] : SSet.{u}) = intervalParameterPoint v := rfl

end SerrePositivity.KST.SConstruction
