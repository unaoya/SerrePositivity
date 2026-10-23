module

public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoin

/-!
概要：射 X→Y の写像円柱から relative join X⋆_Y Y への標準比較。
方針：区間付き対角の自然性で円柱の射を引き戻しへ持ち上げ、終端を Y に貼る。
規約：ここでは比較射と計算則を構成し、その同値性は別に証明する。
使われ方：Kerodon Proposition 5.2.4.5、1 単体上の scaffold 比較の標準射。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：射 f の区間付き対角を relative join f id へ写す。
方針：左の係数をそのまま保ち、右の係数を f で写して引き戻しへ持ち上げる。
規約：基底の円柱の係数は f で写す。
使われ方：Kerodon Proposition 5.2.4.5、写像円柱の円柱部分の比較。 -/
noncomputable def relativeJoinPrism {X Y : SSet.{u}} (f : X ⟶ Y) :
    (Δ[1] : SSet.{u}) ⊗ X ⟶ relativeJoin f (𝟙 Y) :=
  pullback.lift (joinDiagonal X ≫ joinMap (𝟙 X) f) ((Δ[1] : SSet.{u}) ◁ f) (by
    rw [Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id]
    exact (joinDiagonal_naturality f).symm)

/-- 概要：relative join への prism の零端は左包含。
方針：引き戻しの両射影に対して対角の零端と prism の自然性を計算する。
規約：左因子は X。
使われ方：Kerodon Proposition 5.2.4.5、写像円柱の始点の係数値の固定。 -/
lemma relativeJoinPrism_zero {X Y : SSet.{u}} (f : X ⟶ Y) :
    prismEndpoint 0 X ≫ relativeJoinPrism f = relativeJoinInl f (𝟙 Y) := by
  apply pullback.hom_ext
  · rw [relativeJoinPrism, Category.assoc, pullback.lift_fst,
      ← Category.assoc, prismEndpoint_zero_joinDiagonal, joinInl_joinMap, Category.id_comp,
      relativeJoinInl_fst]
  · rw [relativeJoinPrism, Category.assoc, pullback.lift_snd]
    rw [relativeJoinInl, pullback.lift_snd]
    exact prismEndpoint_naturality 0 f

/-- 概要：relative join への prism の一端は f と右包含の合成。
方針：引き戻しの両射影で対角の一端を計算する。
規約：一端で X の係数を f で Y の係数へ移す。
使われ方：Kerodon Proposition 5.2.4.5、写像円柱の貼り合わせの条件。 -/
lemma relativeJoinPrism_one {X Y : SSet.{u}} (f : X ⟶ Y) :
    prismEndpoint 1 X ≫ relativeJoinPrism f = f ≫ relativeJoinInr f (𝟙 Y) := by
  apply pullback.hom_ext
  · rw [relativeJoinPrism, Category.assoc, pullback.lift_fst,
      ← Category.assoc, prismEndpoint_one_joinDiagonal, joinInr_joinMap,
      Category.assoc, relativeJoinInr_fst]
  · rw [relativeJoinPrism, Category.assoc, pullback.lift_snd]
    rw [Category.assoc, relativeJoinInr, pullback.lift_snd, Category.id_comp]
    exact prismEndpoint_naturality 1 f

/-- 概要：relative join への prism は標準区間上の射。
方針：引き戻しの第二射影の式の区間成分を取る。
規約：円柱の第二成分は射影で忘れる。
使われ方：Kerodon Proposition 5.2.4.5、区間上の比較の底の可換性。 -/
lemma relativeJoinPrism_projection {X Y : SSet.{u}} (f : X ⟶ Y) :
    relativeJoinPrism f ≫ relativeJoinProjection f (𝟙 Y) = fst (Δ[1] : SSet.{u}) X := by
  rw [relativeJoinProjection, ← Category.assoc]
  rw [show relativeJoinPrism f ≫ pullback.snd _ _ = ((Δ[1] : SSet.{u}) ◁ f) from
    pullback.lift_snd _ _ _]
  rfl

/-- 概要：射 f の写像円柱から relative join f id への標準比較射。
方針：prism の終端の公式で円柱部分と Y の包含を pushout から貼る。
規約：射の同値性は構成の仮定にも結論にも含めない。
使われ方：Kerodon Proposition 5.2.4.5、1 単体上の scaffold の全体比較の射。 -/
noncomputable def relativeJoinCylinderComparison {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout (prismEndpoint 1 X) f ⟶ relativeJoin f (𝟙 Y) :=
  pushout.desc (relativeJoinPrism f) (relativeJoinInr f (𝟙 Y)) (relativeJoinPrism_one f)

/-- 概要：写像円柱の比較は円柱部分で指定した prism を回収する。
方針：pushout の左包含の計算則を使う。
規約：円柱部分は Δ[1]×X。
使われ方：Kerodon Proposition 5.2.4.5、比較射の円柱上の計算。 -/
lemma relativeJoinCylinderComparison_inl {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout.inl (prismEndpoint 1 X) f ≫ relativeJoinCylinderComparison f = relativeJoinPrism f :=
  pushout.inl_desc _ _ _

/-- 概要：写像円柱の比較は終域部分で relative join の右包含を回収する。
方針：pushout の右包含の計算則を使う。
規約：終域部分は Y。
使われ方：Kerodon Proposition 5.2.4.5、比較射の終端の固定。 -/
lemma relativeJoinCylinderComparison_inr {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout.inr (prismEndpoint 1 X) f ≫ relativeJoinCylinderComparison f =
      relativeJoinInr f (𝟙 Y) :=
  pushout.inr_desc _ _ _

end SerrePositivity.InfinityCategories
