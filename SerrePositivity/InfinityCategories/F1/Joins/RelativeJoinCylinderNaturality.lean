module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingCylinderOverFunctor
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinLeftFunctor
public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinCylinder

/-!
概要：終域を固定した写像円柱から relative join への比較の自然性。
方針：引き戻しの両射影で prism と右包含の自然性を示し、pushout から貼る。
規約：射は通常の圏 Over S の射として扱う。
使われ方：Kerodon Proposition 5.2.4.5、セル分解に沿う比較射の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右包含は底を保つ左因子の射について自然。
方針：引き戻しの第一射影で join の自然性、第二射影で底の固定を使う。
規約：右因子は底 S の恒等射。
使われ方：Kerodon Proposition 5.2.4.5、比較の終域部分の自然性。 -/
lemma relativeJoinInr_leftMap {S : SSet.{u}} {A B : Over S} (u : A ⟶ B) :
    relativeJoinInr A.hom (𝟙 S) ≫ relativeJoinLeftMap (𝟙 S) u.left u.w =
      relativeJoinInr B.hom (𝟙 S) := by
  apply pullback.hom_ext
  · rw [Category.assoc, relativeJoinLeftMap_fst, ← Category.assoc,
      relativeJoinInr_fst, joinInr_joinMap, Category.id_comp, relativeJoinInr_fst]
  · rw [Category.assoc, relativeJoinLeftMap_snd]
    rw [relativeJoinInr, pullback.lift_snd, relativeJoinInr, pullback.lift_snd]

/-- 概要：relative join への prism は底上の左因子の射について自然。
方針：join の対角の自然性と Over の可換条件を両射影で使う。
規約：区間は左因子、右因子は共通の底。
使われ方：Kerodon Proposition 5.2.4.5、比較の円柱部分の自然性。 -/
lemma relativeJoinPrism_naturality {S : SSet.{u}} {A B : Over S} (u : A ⟶ B) :
    relativeJoinPrism A.hom ≫ relativeJoinLeftMap (𝟙 S) u.left u.w =
      ((Δ[1] : SSet.{u}) ◁ u.left) ≫ relativeJoinPrism B.hom := by
  unfold relativeJoinPrism
  apply pullback.hom_ext
  · rw [Category.assoc, relativeJoinLeftMap_fst, ← Category.assoc,
      pullback.lift_fst, Category.assoc, ← joinMap_comp,
      Category.id_comp, Category.comp_id, Category.assoc, pullback.lift_fst,
      ← Category.assoc, joinDiagonal_naturality, Category.assoc, ← joinMap_comp,
      Category.comp_id, u.w]
  · rw [Category.assoc, relativeJoinLeftMap_snd, pullback.lift_snd,
      Category.assoc, pullback.lift_snd, ← whiskerLeft_comp, u.w]

/-- 概要：写像円柱から relative join への標準比較は底上で自然。
方針：pushout の二つの包含上で prism と右包含の自然性を使う。
規約：同じ底 S に向かう射の間の自然性。
使われ方：Kerodon Proposition 5.2.4.5、比較の pushout への接続。 -/
lemma relativeJoinCylinderComparison_naturality {S : SSet.{u}} {A B : Over S}
    (u : A ⟶ B) :
    mappingCylinderOverMap u ≫ relativeJoinCylinderComparison B.hom =
      relativeJoinCylinderComparison A.hom ≫ relativeJoinLeftMap (𝟙 S) u.left u.w := by
  apply pushout.hom_ext
  · rw [← Category.assoc, mappingCylinderOverMap_inl, Category.assoc,
      relativeJoinCylinderComparison_inl, ← Category.assoc,
      relativeJoinCylinderComparison_inl, relativeJoinPrism_naturality]
  · rw [← Category.assoc, mappingCylinderOverMap_inr,
      relativeJoinCylinderComparison_inr, ← Category.assoc,
      relativeJoinCylinderComparison_inr, relativeJoinInr_leftMap]

/-- 概要：写像円柱比較を終域を固定した関手間の自然変換にまとめる。
方針：各構造射の標準比較を成分とし、比較の自然性を使う。
規約：始域は写像円柱関手、終域は右因子を恒等射とする relative join 関手。
使われ方：Kerodon Proposition 5.2.4.5、セルを貼る際の比較射の立方体。 -/
noncomputable def relativeJoinCylinderComparisonNat (S : SSet.{u}) :
    mappingCylinderOverFunctor S ⟶ relativeJoinLeftFunctor (𝟙 S) where
  app A := relativeJoinCylinderComparison A.hom
  naturality _ _ u := relativeJoinCylinderComparison_naturality u

end SerrePositivity.InfinityCategories
