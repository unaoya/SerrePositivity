module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinder
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FatJoinPointCylinder
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinGeneralComparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：終域が標準零単体である写像円柱から relative join への比較の同値性。
方針：写像円柱を一点との fat join、relative join を一点との通常の join と同定する。
規約：始域 X の有限性や quasicategory 性は要求しない。
使われ方：Kerodon Example 5.2.4.6（Tag 024S）、Proposition 5.2.4.5（Tag 024R）、終域の次元零の比較。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：標準零単体の対角円柱の射は同型。
方針：右の点を除く射影の同型と対称性との合成の式を使う。
規約：円柱の係数は標準零単体。
使われ方：Kerodon Example 5.2.3.5（Tag 0246）、点を底とする relative join の計算。 -/
instance joinDiagonalCylinder_point_isIso : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonalCylinder (Δ[0] : SSet.{u})) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonalCylinder (Δ[0] : SSet.{u}) ≫
      fst ((Δ[0] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) (Δ[0] : SSet.{u}) =
        (β_ (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u})).hom := rfl
  exact IsIso.of_isIso_fac_right h

/-- 概要：標準零単体の区間付き対角から通常の join への射は同型。
方針：点の対角円柱の同型と、二つの点の join の円柱比較の同型を合成する。
規約：標準零単体をモノイダル単位と同一視しない。
使われ方：Kerodon Example 5.2.3.5（Tag 0246）、通常の join との同型の引き戻し。 -/
@[kerodon 0246]
instance joinDiagonal_point_isIso : IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal (Δ[0] : SSet.{u})) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal
  infer_instance

/-- 概要：一点を共通の底とする relative join の通常の join への射影は同型。
方針：引き戻す対角射が同型であることを使う。
規約：左右の単体集合と点への射は任意。
使われ方：Kerodon Example 5.2.3.5（Tag 0246）、relative join の通常の join への模型変更。 -/
@[kerodon 0246]
instance relativeJoin_point_fst_isIso {X Y : SSet.{u}}
    (f : X ⟶ (Δ[0] : SSet.{u})) (g : Y ⟶ (Δ[0] : SSet.{u})) :
    IsIso (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal (Δ[0] : SSet.{u}))) := by
  infer_instance

/-- 概要：一点との fat join への prism の比較は relative join の prism の通常の join 表示。
方針：係数の点への射の一意性で円柱の射を同定し、join の円柱比較の自然性を使う。
規約：比較先は join X Δ[0]。
使われ方：Kerodon Example 5.2.4.6（Tag 024S）、二つの比較射の円柱部分の一致。 -/
lemma fatJoinPointPrism_comparison {X : SSet.{u}} (f : X ⟶ (Δ[0] : SSet.{u})) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.fatJoinPointPrism X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison X (Δ[0] : SSet.{u}) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 X) f := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonalCylinder X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap (𝟙 X) f =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.fatJoinPointCylinderIso X).inv := by
    apply CartesianMonoidalCategory.hom_ext
    · change (β_ (Δ[1] : SSet.{u}) X).hom = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.fatJoinPointCylinderIso X).inv ≫
        fst (X ⊗ (Δ[1] : SSet.{u})) (Δ[0] : SSet.{u})
      dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.fatJoinPointCylinderIso, Iso.trans_inv, asIso_inv]
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rfl
    · exact stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.fatJoinPointPrism, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_comparison, ← h,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_naturality, ← Category.assoc]
  rfl

/-- 概要：終域が一点の場合、写像円柱比較は fat join 比較と同型を通じて一致する。
方針：写像円柱の両包含で比較し、円柱部分の公式と join の包含の公式を使う。
規約：この等式は始域 X の充填性を仮定しない。
使われ方：Kerodon Example 5.2.4.6（Tag 024S）、既存の fat join 同値判定との接続。 -/
lemma relativeJoinCylinderComparison_point_fst {X : SSet.{u}} (f : X ⟶ (Δ[0] : SSet.{u})) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison f ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 (Δ[0] : SSet.{u})))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal (Δ[0] : SSet.{u})) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderFatJoinPointIso f).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison X (Δ[0] : SSet.{u}) := by
  apply pushout.hom_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inl,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism, pullback.lift_fst, ← Category.assoc]
    rw [show pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderFatJoinPointIso f).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.fatJoinPointPrism X from (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.fatJoinPointPrism_isPushout f).inl_isoPushout_inv]
    exact (fatJoinPointPrism_comparison f).symm
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inr, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_fst,
      ← Category.assoc]
    rw [show pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderFatJoinPointIso f).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr X (Δ[0] : SSet.{u}) from (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.fatJoinPointPrism_isPushout f).inr_isoPushout_inv,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_comparison]

/-- 概要：任意の単体集合から一点への射の写像円柱比較は前合成の同値条件を満たす。
方針：左右の厳密な同型を消去し、一般の fat join 比較の同値条件を適用する。
規約：始域の Kan 性、有限性、quasicategory 性は不要。
使われ方：Kerodon Example 5.2.4.6（Tag 024S）、Proposition 5.2.4.5（Tag 024R） の終域の次元零の場合。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_point
    {X : SSet.{u}} (f : X ⟶ (Δ[0] : SSet.{u})) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison f) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (asIso
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 (Δ[0] : SSet.{u}))) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal (Δ[0] : SSet.{u}))))).cancel_right
  exact (congrArg (fun g : pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) f ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X (Δ[0] : SSet.{u}) ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence g) (relativeJoinCylinderComparison_point_fst f)).mpr
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderFatJoinPointIso f)).comp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_fatJoinComparison X (Δ[0] : SSet.{u})))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
