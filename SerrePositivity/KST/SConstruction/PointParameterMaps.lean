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

/-- 指定点の写像像で全パラメータを固定する写像は、元の同じ全族の後合成像。 -/
lemma pointParameterMap_post {P Q T : SSet.{u}} (v : P _⦋0⦌) (p : P ⟶ Q) :
    pointParameterMap v T ≫ (p ▷ T) = pointParameterMap (p.app (Opposite.op ⦋0⦌) v) T := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [pointParameterMap, Category.assoc, whiskerRight_fst, lift_fst]
    rw [← Category.assoc, lift_fst, SSet.const_comp]
  · simp only [pointParameterMap, Category.assoc, whiskerRight_snd, lift_snd]

/-- 元の零単体表示で指定点を写すと、同じ全パラメータ制限が厳密に可換する。 -/
lemma pointParameterMap_post_point {P Q T : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ P)
    (p : P ⟶ Q) :
    pointParameterMap (SSet.yonedaEquiv a) T ≫ (p ▷ T) =
      pointParameterMap (SSet.yonedaEquiv (a ≫ p)) T := by
  rw [pointParameterMap_post, SSet.yonedaEquiv_comp]

end SerrePositivity.KST.SConstruction
