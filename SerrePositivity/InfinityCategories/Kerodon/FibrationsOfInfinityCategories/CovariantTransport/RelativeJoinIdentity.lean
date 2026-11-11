module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinder
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：恒等射の relative join と写像円柱の比較の厳密な同型性。
方針：join の恒等射の引き戻しを区間付き係数と同定し、比較の円柱上の式で戻す。
規約：単体集合 S の quasicategory 性は不要。
使われ方：Kerodon Example 5.2.3.6（Tag 0247）、Proposition 5.2.4.5（Tag 024R）、relative join の恒等の場合の検査。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：恒等射どうしの relative join の引き戻しの第二射影は同型。
方針：joinMap id id が恒等射であることを使う。
規約：射影先は Δ[1]×S。
使われ方：Kerodon Example 5.2.3.6（Tag 0247）、relative join の円柱表示。 -/
instance relativeJoinSelf_snd_isIso (S : SSet.{u}) :
    IsIso (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 S) (𝟙 S)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S)) := by
  have : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 S) (𝟙 S)) := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id]; infer_instance
  infer_instance

/-- 概要：恒等射どうしの relative join は元の単体集合の円柱と同型。
方針：引き戻しの第二射影を順方向に使う。
規約：通常の区間が第一因子となる。
使われ方：Kerodon Example 5.2.3.6（Tag 0247）、relative join の同じ係数の両端の同定。 -/
@[kerodon 0247]
noncomputable def relativeJoinSelfIso (S : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 S) (𝟙 S) ≅ (Δ[1] : SSet.{u}) ⊗ S :=
  asIso (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 S) (𝟙 S)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S))

/-- 概要：恒等射の relative join への prism は同型。
方針：第二射影との合成が恒等になることから、同型の逆射と同定する。
規約：この prism 自体が円柱との比較の逆射になる。
使われ方：Kerodon Example 5.2.3.6（Tag 0247）、写像円柱比較の恒等の場合。 -/
instance relativeJoinPrism_id_isIso (S : SSet.{u}) : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism (𝟙 S)) := by
  let q := pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 S) (𝟙 S)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S)
  have : IsIso q := relativeJoinSelf_snd_isIso S
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism (𝟙 S) = inv q := by
    apply (cancel_mono q).1
    rw [IsIso.inv_hom_id]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism (𝟙 S) ≫ pullback.snd _ _ = 𝟙 _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism, pullback.lift_snd, whiskerLeft_id]
  rw [he]
  infer_instance

/-- 概要：恒等射の写像円柱から relative join への比較射は同型。
方針：写像円柱の円柱部分の包含と relative join への prism が両方同型であることを使う。
規約：一般の射の比較の同値性をここから推論しない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、構成した比較射の恒等の場合の検査。 -/
instance relativeJoinCylinderComparison_id_isIso (S : SSet.{u}) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison (𝟙 S)) := by
  let j := pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 S) (𝟙 S)
  have : IsIso j := by dsimp only [j]; infer_instance
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison (𝟙 S) = inv j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism (𝟙 S) := by
    apply (cancel_epi j).1
    rw [IsIso.hom_inv_id_assoc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inl (𝟙 S)
  rw [he]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
