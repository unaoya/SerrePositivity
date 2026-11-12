module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.CosliceAlternatingTower
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinRightBoundaryAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NervePosetUniverse

/-!
概要：固定入力の下で、始点を持つ順序図式の余極限を底から構成する。
方針：右包含を既存の右余錐頂点と相対 join 境界に分解して共終性を示す。
規約：入力図式の余極限や底の全小余極限を要求しない。
使われ方：長さ κ₀ の相対交互構成の最終余極限。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：左 anodyne な指定初点を持つ右因子への join 右包含は right anodyne。
方針：右余錐頂点の pushout と相対 join 境界の inner anodyne 性を合成する。
規約：左因子は任意。
使われ方：入力付き順序余極限を底で構成するための共終性。 -/
lemma joinInr_rightAnodyne_of_leftAnodyne_point {L : SSet.{u}}
    (K : SSet.{u}) (i : (Δ[0] : SSet.{u}) ⟶ L) [Mono i]
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L) := by
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0]) i) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.of_isPushout (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0]) i).flip
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneTip_rightAnodyne K)
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryMap i K) := by
    intro E B p hp
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p := ⟨hp⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightBoundaryMap_innerAnodyne_of_leftAnodyne i K hi p InnerFibration.mem
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinRightBoundaryMap_right i K]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.comp_mem _ _ hp hb

/-- 概要：始点を持つ元の順序 nerve への右 join 包含は right cofinal。
方針：始点包含の left anodyne 性を元の相対 join 境界へ渡す。
規約：固定入力の形状には大きさの制限を課さない。
使われ方：固定始域の下の順序余極限。 -/
lemma joinInr_orderBot_isRightCofinal (K : SSet.{u}) (I : Type u)
    [Preorder I] [OrderBot I] : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (nerve I)) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne _
    (joinInr_rightAnodyne_of_leftAnodyne_point K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (⊥ : I))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint_leftAnodyne (isInitialBot (α := I))))

/-- 概要：宇宙を持ち上げた同じ始点付き順序でも右 join 包含は right cofinal。
方針：元の順序を ULift 順序の nerve に同定し、同型を相殺する。
規約：元の大きい固定入力を変更しない。
使われ方：長さ κ₀ の元の全交互図式とその両成分。 -/
lemma joinInr_ulift_orderBot_isRightCofinal (K : SSet.{max u v}) (I : Type u)
    [Preorder I] [OrderBot I] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K ((SSet.uliftFunctor.{v, u}).obj (nerve I))) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nervePosetUniverseIso.{u, v} I
  have h := ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso e.hom).comp
    (joinInr_orderBot_isRightCofinal K (ULift.{v} I))).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (Iso.refl K) e).inv)
  have he : (e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (nerve (ULift.{v} I))) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (Iso.refl K) e).inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K ((SSet.uliftFunctor.{v, u}).obj (nerve I)) := by
    change (e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) e.inv = _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap]
    simp only [Category.id_comp, ← Category.assoc, e.hom_inv_id]
  exact he ▸ h

/-- 概要：固定始域の下の始点付き順序図式の余極限は底の存在から構成できる。
方針：右 join 包含の共終性を既存の反復 coslice 比較に渡す。
規約：元の底の余極限だけを使う。
使われ方：入力付き相対交互構成の最終余極限の存在。 -/
lemma fixedSource_orderBot_hasColimit {K C : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory C] (a : K ⟶ C)
    (I : Type u) [Preorder I] [OrderBot I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)
    (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCoslice_hasColimit_of_rightCofinal a D
    (joinInr_ulift_orderBot_isRightCofinal K I) hD

/-- 概要：同じ固定始域内の順序余錐の余極限性は底で判定される。
方針：同じ右包含の共終性と既存の余錐圏比較を使う。
規約：元の全余錐を選び直さない。
使われ方：両成分余極限の底への保存と同じ入力上での比較。 -/
lemma fixedSource_orderBot_isColimitCone_iff_projection {K C : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory C] (a : K ⟶ C)
    (I : Type u) [Preorder I] [OrderBot I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a) c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCoslice_isColimitCone_iff_projection a D
    (joinInr_ulift_orderBot_isRightCofinal K I) c

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
