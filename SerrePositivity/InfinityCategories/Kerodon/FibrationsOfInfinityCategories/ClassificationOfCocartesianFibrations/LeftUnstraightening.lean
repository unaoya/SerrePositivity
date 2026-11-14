module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaces
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：𝒮 値の coherent diagram の left unstraightening の全空間と射影。
方針：pointed space の射影を図式に沿って引き戻す。
規約：fiber の値との同値と分類定理は後続の証明課題として区別する。
使われ方：Kerodon Example 5.6.2.9（Tag 026S）、Corollary 5.6.0.6（Tag 028T） の left fibration 側の構成。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：𝒮 値の関手の left unstraightening の全空間。
方針：pointed space の射影との引き戻しを取る。
規約：F は任意の coherent diagram で、strict diagram に制限しない。
使われ方：Kerodon Example 5.6.2.9（Tag 026S）、空間値 unstraightening の対象の構成。 -/
@[kerodon 026S]
noncomputable def leftUnstraightening {C : SSet.{u + 1}} (F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    SSet.{u + 1} := pullback _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F

/-- 概要：left unstraightening の底への射影。
方針：引き戻しの第二射影を取る。
規約：底は元の図式の定義域 C。
使われ方：Kerodon Example 5.6.2.9（Tag 026S）、構成された left fibration。 -/
noncomputable def leftUnstraighteningProjection {C : SSet.{u + 1}}
    (F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) : leftUnstraightening F ⟶ C :=
  pullback.snd _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F

/-- 概要：構成した unstraightening の射影は left fibration。
方針：pointed space の射影の left fibration 性を底変換する。
規約：底 C の quasicategory 性は要求しない。
使われ方：Kerodon Example 5.6.2.9（Tag 026S）、分類の構成方向の充填性。 -/
@[kerodon 026S]
instance leftUnstraighteningProjection_leftFibration {C : SSet.{u + 1}}
    (F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (leftUnstraighteningProjection F) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem⟩

/-- 概要：底が quasicategory なら unstraightening の全空間も quasicategory。
方針：射影の inner fibration 性を使う。
規約：任意の coherent diagram F を扱う。
使われ方：Kerodon Example 5.6.2.9（Tag 026S）、通常の圏の nerve 上の構成の特別な場合。 -/
instance leftUnstraightening_quasicategory {C : SSet.{u + 1}} [Quasicategory C]
    (F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) : Quasicategory (leftUnstraightening F) :=
  quasicategory_of_innerFibration (leftUnstraighteningProjection F)

/-- 概要：𝒮 上で可換な底の射は unstraightening の全空間の射を与える。
方針：pointed space 成分を保ち、底の成分を α で写す。
規約：h は α の後に G を適用すると F になる厳密な等式。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、unstraightening の底変換の比較射。 -/
noncomputable def leftUnstraighteningMap {C D : SSet.{u + 1}}
    (F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (G : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (α : C ⟶ D) (h : α ≫ G = F) : leftUnstraightening F ⟶ leftUnstraightening G :=
  pullback.lift (pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F)
    (leftUnstraighteningProjection F ≫ α) (by
      rw [Category.assoc, h]
      exact pullback.condition)

/-- 概要：底変換の比較射は pointed space 成分を保つ。
方針：引き戻しへの持ち上げの第一成分を計算する。
規約：α と可換性の証明 h は任意。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、底変換の合成の確認。 -/
lemma leftUnstraighteningMap_pointed {C D : SSet.{u + 1}}
    (F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (G : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (α : C ⟶ D) (h : α ≫ G = F) :
    leftUnstraighteningMap F G α h ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection G =
      pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F := pullback.lift_fst _ _ _

/-- 概要：底変換の比較射は元の底の射 α を被覆する。
方針：引き戻しへの持ち上げの第二成分を計算する。
規約：両側の射影は leftUnstraighteningProjection。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、底上の比較図式。 -/
lemma leftUnstraighteningMap_projection {C D : SSet.{u + 1}}
    (F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (G : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (α : C ⟶ D) (h : α ≫ G = F) :
    leftUnstraighteningMap F G α h ≫ leftUnstraighteningProjection G =
      leftUnstraighteningProjection F ≫ α := pullback.lift_snd _ _ _

/-- 概要：恒等の底の射による unstraightening の比較射は恒等射。
方針：引き戻しの両射影で確認する。
規約：可換性の証明の違いは証明無関係性で除かれる。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、底の射に関する関手性。 -/
lemma leftUnstraighteningMap_id {C : SSet.{u + 1}} (F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    leftUnstraighteningMap F F (𝟙 C) (Category.id_comp F) = 𝟙 (leftUnstraightening F) := by
  apply pullback.hom_ext
  · simp only [leftUnstraighteningMap, Category.id_comp, pullback.lift_fst]
  · simp only [leftUnstraighteningMap, leftUnstraighteningProjection,
      Category.comp_id, Category.id_comp, pullback.lift_snd]

/-- 概要：底の射の合成による比較射は比較射の合成と一致する。
方針：引き戻しの二成分と結合律を計算する。
規約：F、G、H はそれぞれの底から同じ 𝒮 への図式。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、底の射に関する unstraightening の合成則。 -/
lemma leftUnstraighteningMap_comp {C D E : SSet.{u + 1}}
    (F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (G : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (H : E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (α : C ⟶ D) (β : D ⟶ E)
    (hα : α ≫ G = F) (hβ : β ≫ H = G) :
    leftUnstraighteningMap F H (α ≫ β) (by rw [Category.assoc, hβ, hα]) =
      leftUnstraighteningMap F G α hα ≫ leftUnstraighteningMap G H β hβ := by
  apply pullback.hom_ext
  · simp only [leftUnstraighteningMap, Category.assoc, pullback.lift_fst]
  · simp only [leftUnstraighteningMap, leftUnstraighteningProjection,
      Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

/-- 概要：底の可換な射による unstraightening の比較四角形は引き戻し。
方針：pointed space の射影との二つの引き戻しから右の四角形を消去する。
規約：底や図式の quasicategory 性は不要。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、unstraightening の厳密な底変換。 -/
lemma leftUnstraighteningMap_isPullback {C D : SSet.{u + 1}}
    (F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (G : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (α : C ⟶ D) (h : α ≫ G = F) :
    IsPullback (leftUnstraighteningMap F G α h) (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection G) α := by
  apply ((IsPullback.of_hasPullback _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection G).paste_horiz_iff
    (leftUnstraighteningMap_projection F G α h)).mp
  rw [leftUnstraighteningMap_pointed, h]
  exact IsPullback.of_hasPullback _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "3.3.2.8" (partial := stronger-hyp) "仮定：小さい left fibration p:X→S に加え S が準圏（Lean が強い）。結論：nativeLeftTransportRepresentation p の図式 S→SpaceInfinity の、pointSpaceVertex からの coslice の引戻しへ、底を厳密に保つ前合成同値がある（一致）。任意の単体的 S に対して同じ比較を同値とする型はない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection
