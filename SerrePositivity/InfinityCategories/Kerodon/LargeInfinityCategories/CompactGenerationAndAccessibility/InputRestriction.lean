module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.StableInputLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftFibrationCoconeTarget
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationEquivalenceLifting

/-!
概要：追加入力を忘れる二重 slice の全制限を構成する。
方針：固定始域の制限を標的上へ送り、元の図式と余錐の等式で表示を合わせる。
規約：全単体値を保持し、入力の単射性は同値持ち上げだけに使う。
使われ方：指定成分始点を保持する相対交互構成の共通入力への比較。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility


/-- 概要：固定始域制限と表示移送を組み合わせた元の入力への制限。
方針：元の coslice 制限の終域だけを指定された図式に合わせる。
規約：入力図式の等式を明示する。
使われ方：二重 slice の制限の基礎。 -/
def stableCosliceRestriction {K L C : SSet.{u}} (q : K ⟶ C) (i : L ⟶ K)
    (r : L ⟶ C) (hi : i ≫ q = r) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder r :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict q i ≫ eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder hi)

/-- 概要：固定始域の制限は元の全余錐の指定制限を点として保つ。
方針：Yoneda 表示と等号移送の全値を計算する。
規約：全余錐の厳密な等式を使う。
使われ方：固定標的の表示合わせ。 -/
lemma stableCosliceRestriction_cocone_point {K L C : SSet.{u}}
    (q : K ⟶ C) (i : L ⟶ K) (r : L ⟶ C) (hi : i ≫ q = r)
    (z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0]) ≫ z.val = t.val) :
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q)).symm z ≫ stableCosliceRestriction q i r hi =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder r)).symm t := by
  rw [SSet.yonedaEquiv_symm_comp]
  apply congrArg ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder r)).symm)
  apply Subtype.ext
  change ((eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder hi)).hom.app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict q i).app (Opposite.op ⦋0⦌) z)).val = t.val
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnder_eqToIso_val hi]
  exact hz

/-- 概要：元の入力と標的を同時に合わせる全制限。
方針：始域制限を固定標的上へ送って表示を等号で合わせる。
規約：元の全余錐の指定制限を保持する。
使われ方：異なる追加入力からの共通入力への比較。 -/
def stableInputRestriction {K L C : SSet.{u}}
    (q : K ⟶ C) (i : L ⟶ K) (r : L ⟶ C) (hi : i ≫ q = r)
    (z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0]) ≫ z.val = t.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q)).symm z) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder r)).symm t) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q)).symm z)
    (stableCosliceRestriction q i r hi) ≫
      eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (stableCosliceRestriction_cocone_point q i r hi z t hz))

/-- 概要：二重制限は全増大余錐族を元の始域制限で送る。
方針：標的の表示移送を消し、slice 後合成の全展開を使う。
規約：任意のパラメータを持つ全族の等式。
使われ方：表示の余極限性と基底射影の回収。 -/
lemma stableInputRestriction_uncurry {K L C A : SSet.{u}}
    (q : K ⟶ C) (i : L ⟶ K) (r : L ⟶ C) (hi : i ≫ q = r)
    (z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0]) ≫ z.val = t.val)
    (P : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q)).symm z)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (P ≫ stableInputRestriction q i r hi z t hz) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry P ≫ stableCosliceRestriction q i r hi := by
  rw [stableInputRestriction, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceOverUncurry_eqToHom (stableCosliceRestriction_cocone_point q i r hi z t hz),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_postcomp]

/-- 概要：元の対象圏への全射影は追加入力の制限で変わらない。
方針：固定始域の制限と図式の等号移送の射影を合成する。
規約：元の対象圏内の全射の厳密な等式。
使われ方：component compact 性を制限前後で同定する。 -/
lemma stableCosliceRestriction_projection {K L C : SSet.{u}}
    (q : K ⟶ C) (i : L ⟶ K) (r : L ⟶ C) (hi : i ≫ q = r) :
    stableCosliceRestriction q i r hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection r = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q := by
  cases hi
  simpa only [stableCosliceRestriction, eqToHom_refl, Category.comp_id] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection q i

/-- 概要：単射の追加入力を忘れる二重制限は同値を持ち上げる。
方針：coslice 制限の左ファイブレーションと標的上の同値持ち上げを合成する。
規約：元の対象圏の quasicategory 性と入力の単射性のみを使う。
使われ方：追加入力を保持したまま共通像を厳密に合わせる。 -/
lemma stableInputRestriction_equivalenceLifting {K L C : SSet.{u}} [Quasicategory C]
    (q : K ⟶ C) (i : L ⟶ K) [Mono i] (r : L ⟶ C) (hi : i ≫ q = r)
    (z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0]) ≫ z.val = t.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (stableInputRestriction q i r hi z t hz) := by
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (stableCosliceRestriction q i r hi) := by
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict q i) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceUnderRestrict_leftFibration_of_mono q i
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict q i) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_equivalenceLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict q i)
    intro A B j hj he
    have := h j hj he
    dsimp only [stableCosliceRestriction]
    infer_instance
  have hO : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp
      ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q)).symm z) (stableCosliceRestriction q i r hi)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.sliceOverPostcomp_equivalenceLifting _ _ hR
  dsimp only [stableInputRestriction]
  intro A B j hj he
  have := hO j hj he
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
