module

public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinCylinder
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
概要：恒等射の relative join と写像円柱の比較の厳密な同型性。
方針：join の恒等射の引き戻しを区間付き係数と同定し、比較の円柱上の式で戻す。
規約：単体集合 S の quasicategory 性は不要。
使われ方：Kerodon Example 5.2.3.6、Proposition 5.2.4.5、relative join の恒等の場合の検査。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：恒等射どうしの relative join の引き戻しの第二射影は同型。
方針：joinMap id id が恒等射であることを使う。
規約：射影先は Δ[1]×S。
使われ方：Kerodon Example 5.2.3.6、relative join の円柱表示。 -/
instance relativeJoinSelf_snd_isIso (S : SSet.{u}) :
    IsIso (pullback.snd (joinMap (𝟙 S) (𝟙 S)) (joinDiagonal S)) := by
  have : IsIso (joinMap (𝟙 S) (𝟙 S)) := by rw [joinMap_id]; infer_instance
  infer_instance

/-- 概要：恒等射どうしの relative join は元の単体集合の円柱と同型。
方針：引き戻しの第二射影を順方向に使う。
規約：通常の区間が第一因子となる。
使われ方：Kerodon Example 5.2.3.6、relative join の同じ係数の両端の同定。 -/
noncomputable def relativeJoinSelfIso (S : SSet.{u}) :
    relativeJoin (𝟙 S) (𝟙 S) ≅ (Δ[1] : SSet.{u}) ⊗ S :=
  asIso (pullback.snd (joinMap (𝟙 S) (𝟙 S)) (joinDiagonal S))

/-- 概要：恒等射の relative join への prism は同型。
方針：第二射影との合成が恒等になることから、同型の逆射と同定する。
規約：この prism 自体が円柱との比較の逆射になる。
使われ方：Kerodon Example 5.2.3.6、写像円柱比較の恒等の場合。 -/
instance relativeJoinPrism_id_isIso (S : SSet.{u}) : IsIso (relativeJoinPrism (𝟙 S)) := by
  let q := pullback.snd (joinMap (𝟙 S) (𝟙 S)) (joinDiagonal S)
  have : IsIso q := relativeJoinSelf_snd_isIso S
  have he : relativeJoinPrism (𝟙 S) = inv q := by
    apply (cancel_mono q).1
    rw [IsIso.inv_hom_id]
    change relativeJoinPrism (𝟙 S) ≫ pullback.snd _ _ = 𝟙 _
    rw [relativeJoinPrism, pullback.lift_snd, whiskerLeft_id]
  rw [he]
  infer_instance

/-- 概要：恒等射の写像円柱から relative join への比較射は同型。
方針：写像円柱の円柱部分の包含と relative join への prism が両方同型であることを使う。
規約：一般の射の比較の同値性をここから推論しない。
使われ方：Kerodon Proposition 5.2.4.5、構成した比較射の恒等の場合の検査。 -/
instance relativeJoinCylinderComparison_id_isIso (S : SSet.{u}) :
    IsIso (relativeJoinCylinderComparison (𝟙 S)) := by
  let j := pushout.inl (prismEndpoint 1 S) (𝟙 S)
  have : IsIso j := by dsimp only [j]; infer_instance
  have he : relativeJoinCylinderComparison (𝟙 S) = inv j ≫ relativeJoinPrism (𝟙 S) := by
    apply (cancel_epi j).1
    rw [IsIso.hom_inv_id_assoc]
    exact relativeJoinCylinderComparison_inl (𝟙 S)
  rw [he]
  infer_instance

end SerrePositivity.InfinityCategories
