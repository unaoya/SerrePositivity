module

public import SerrePositivity.InfinityCategories.F1.RelativeJoinCylinder
public import SerrePositivity.InfinityCategories.F1.FatJoinPointCylinder
public import SerrePositivity.InfinityCategories.Core.FatJoinGeneralComparison

/-!
概要：終域が標準零単体である写像円柱から relative join への比較の同値性。
方針：写像円柱を一点との fat join、relative join を一点との通常の join と同定する。
規約：始域 X の有限性や quasicategory 性は要求しない。
使われ方：Kerodon Example 5.2.4.6、Proposition 5.2.4.5、終域の次元零の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：標準零単体の対角円柱の射は同型。
方針：右の点を除く射影の同型と対称性との合成の式を使う。
規約：円柱の係数は標準零単体。
使われ方：Kerodon Example 5.2.3.5、点を底とする relative join の計算。 -/
instance joinDiagonalCylinder_point_isIso : IsIso (joinDiagonalCylinder (Δ[0] : SSet.{u})) := by
  have h : joinDiagonalCylinder (Δ[0] : SSet.{u}) ≫
      fst ((Δ[0] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) (Δ[0] : SSet.{u}) =
        (β_ (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u})).hom := rfl
  exact IsIso.of_isIso_fac_right h

/-- 概要：標準零単体の区間付き対角から通常の join への射は同型。
方針：点の対角円柱の同型と、二つの点の join の円柱比較の同型を合成する。
規約：標準零単体をモノイダル単位と同一視しない。
使われ方：Kerodon Example 5.2.3.5、通常の join との同型の引き戻し。 -/
instance joinDiagonal_point_isIso : IsIso (joinDiagonal (Δ[0] : SSet.{u})) := by
  unfold joinDiagonal
  infer_instance

/-- 概要：一点を共通の底とする relative join の通常の join への射影は同型。
方針：引き戻す対角射が同型であることを使う。
規約：左右の単体集合と点への射は任意。
使われ方：Kerodon Example 5.2.3.5、relative join の通常の join への模型変更。 -/
instance relativeJoin_point_fst_isIso {X Y : SSet.{u}}
    (f : X ⟶ (Δ[0] : SSet.{u})) (g : Y ⟶ (Δ[0] : SSet.{u})) :
    IsIso (pullback.fst (joinMap f g) (joinDiagonal (Δ[0] : SSet.{u}))) := by
  infer_instance

/-- 概要：一点との fat join への prism の比較は relative join の prism の通常の join 表示。
方針：係数の点への射の一意性で円柱の射を同定し、join の円柱比較の自然性を使う。
規約：比較先は join X Δ[0]。
使われ方：Kerodon Example 5.2.4.6、二つの比較射の円柱部分の一致。 -/
lemma fatJoinPointPrism_comparison {X : SSet.{u}} (f : X ⟶ (Δ[0] : SSet.{u})) :
    fatJoinPointPrism X ≫ fatJoinComparison X (Δ[0] : SSet.{u}) =
      joinDiagonal X ≫ joinMap (𝟙 X) f := by
  have h : joinDiagonalCylinder X ≫ fatJoinCylinderMap (𝟙 X) f =
      (fatJoinPointCylinderIso X).inv := by
    apply CartesianMonoidalCategory.hom_ext
    · change (β_ (Δ[1] : SSet.{u}) X).hom = (fatJoinPointCylinderIso X).inv ≫
        fst (X ⊗ (Δ[1] : SSet.{u})) (Δ[0] : SSet.{u})
      dsimp only [fatJoinPointCylinderIso, Iso.trans_inv, asIso_inv]
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rfl
    · exact stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [fatJoinPointPrism, Category.assoc, fatJoinCylinder_comparison, ← h,
    Category.assoc, joinCylinderMap_naturality, ← Category.assoc]
  rfl

/-- 概要：終域が一点の場合、写像円柱比較は fat join 比較と同型を通じて一致する。
方針：写像円柱の両包含で比較し、円柱部分の公式と join の包含の公式を使う。
規約：この等式は始域 X の充填性を仮定しない。
使われ方：Kerodon Example 5.2.4.6、既存の fat join 同値判定との接続。 -/
lemma relativeJoinCylinderComparison_point_fst {X : SSet.{u}} (f : X ⟶ (Δ[0] : SSet.{u})) :
    relativeJoinCylinderComparison f ≫ pullback.fst (joinMap f (𝟙 (Δ[0] : SSet.{u})))
        (joinDiagonal (Δ[0] : SSet.{u})) =
      (mappingCylinderFatJoinPointIso f).hom ≫ fatJoinComparison X (Δ[0] : SSet.{u}) := by
  apply pushout.hom_ext
  · rw [← Category.assoc, relativeJoinCylinderComparison_inl,
      relativeJoinPrism, pullback.lift_fst, ← Category.assoc]
    rw [show pushout.inl (prismEndpoint 1 X) f ≫ (mappingCylinderFatJoinPointIso f).hom =
      fatJoinPointPrism X from (fatJoinPointPrism_isPushout f).inl_isoPushout_inv]
    exact (fatJoinPointPrism_comparison f).symm
  · rw [← Category.assoc, relativeJoinCylinderComparison_inr, relativeJoinInr_fst,
      ← Category.assoc]
    rw [show pushout.inr (prismEndpoint 1 X) f ≫ (mappingCylinderFatJoinPointIso f).hom =
      fatJoinInr X (Δ[0] : SSet.{u}) from (fatJoinPointPrism_isPushout f).inr_isoPushout_inv,
      fatJoinInr_comparison]

/-- 概要：任意の単体集合から一点への射の写像円柱比較は前合成の同値条件を満たす。
方針：左右の厳密な同型を消去し、一般の fat join 比較の同値条件を適用する。
規約：始域の Kan 性、有限性、quasicategory 性は不要。
使われ方：Kerodon Example 5.2.4.6、Proposition 5.2.4.5 の終域の次元零の場合。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_point
    {X : SSet.{u}} (f : X ⟶ (Δ[0] : SSet.{u})) :
    IsPrecompositionEquivalence (relativeJoinCylinderComparison f) := by
  apply (isPrecompositionEquivalence_of_iso (asIso
    (pullback.fst (joinMap f (𝟙 (Δ[0] : SSet.{u}))) (joinDiagonal (Δ[0] : SSet.{u}))))).cancel_right
  exact (congrArg (fun g : pushout (prismEndpoint 1 X) f ⟶ join X (Δ[0] : SSet.{u}) ↦
    IsPrecompositionEquivalence g) (relativeJoinCylinderComparison_point_fst f)).mpr
      ((isPrecompositionEquivalence_of_iso (mappingCylinderFatJoinPointIso f)).comp
        (isPrecompositionEquivalence_fatJoinComparison X (Δ[0] : SSet.{u})))

end SerrePositivity.InfinityCategories
