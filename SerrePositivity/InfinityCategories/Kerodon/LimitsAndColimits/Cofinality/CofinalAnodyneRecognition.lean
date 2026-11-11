module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFactorization
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：cofinal な単射の anodyne 性と、一般の cofinal な射の因子分解。
方針：cofinal な fibration の全境界充填を使い、単射の場合は因子から持ち上げを戻す。
規約：底と始域に quasicategory 性を課さない。
使われ方：Kerodon Proposition 7.2.1.3（Tag 02N3）、Corollary 7.2.1.15（Tag 02NE）。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet MorphismProperty
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：単射と trivial Kan fibration による因子分解では左持ち上げ性を戻せる。
方針：単射の持ち上げで右因子の切断を取り、左因子の各持ち上げをその切断へ制限する。
規約：P は任意の射の性質。モデル構造は使わない。
使われ方：cofinal な単射が左右 anodyne であることの判定。 -/
lemma cofinalLlp_of_mono_trivialKan_factorization (P : MorphismProperty SSet.{u})
    {X Y Z : SSet.{u}} (i : X ⟶ Y) [Mono i] (j : X ⟶ Z) (p : Z ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (hj : P.rlp.llp j) (he : j ≫ p = i) : P.rlp.llp i := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) i inferInstance
  have sq : CommSq j i p (𝟙 Y) := ⟨by rw [he, Category.comp_id]⟩
  intro A B q hq
  have := hj q hq
  constructor
  intro a b h
  have sq' : CommSq a j q (p ≫ b) := by
    constructor
    rw [← Category.assoc, he]
    exact h.w
  refine CommSq.HasLift.mk' { l := sq.lift ≫ sq'.lift, fac_left := ?_, fac_right := ?_ }
  · rw [← Category.assoc, sq.fac_left, sq'.fac_left]
  · rw [Category.assoc, sq'.fac_right, ← Category.assoc, sq.fac_right, Category.id_comp]

/-- 概要：left cofinal な射は left anodyne な単射と trivial Kan fibration に分解できる。
方針：以前の因子分解の cofinal left fibration 側に全境界の判定を適用する。
規約：合成の一致は厳密な等式。
使われ方：Kerodon Corollary 7.2.1.15（Tag 02NE） の双対。 -/
@[kerodon 02NE]
lemma IsLeftCofinal.exists_anodyne_trivialKan_factorization {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal f) :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (p : Z ⟶ Y),
      Mono i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p ∧ i ≫ p = f := by
  obtain ⟨Z, i, p, hm, hi, hp, hpc, he⟩ := hf.exists_anodyne_fibration_factorization
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p := hp
  exact ⟨Z, i, p, hm, hi, hpc.trivialKanFibration, he⟩

/-- 概要：right cofinal な射は right anodyne な単射と trivial Kan fibration に分解できる。
方針：以前の因子分解の cofinal right fibration 側に可縮 fiber の判定を適用する。
規約：合成の一致は厳密な等式。
使われ方：Kerodon Corollary 7.2.1.15（Tag 02NE）。 -/
lemma IsRightCofinal.exists_anodyne_trivialKan_factorization {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f) :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (p : Z ⟶ Y),
      Mono i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p ∧ i ≫ p = f := by
  obtain ⟨Z, i, p, hm, hi, hp, hpc, he⟩ := hf.exists_anodyne_fibration_factorization
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p := hp
  exact ⟨Z, i, p, hm, hi, hpc.trivialKanFibration, he⟩

/-- 概要：left cofinal な単射は left anodyne。
方針：anodyne と trivial Kan の因子分解から左持ち上げ性を戻す。
規約：単射性が必要。
使われ方：Kerodon Proposition 7.2.1.3（Tag 02N3） の必要性。 -/
lemma IsLeftCofinal.leftAnodyneExtensions {X Y : SSet.{u}} {i : X ⟶ Y} [Mono i]
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal i) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i := by
  obtain ⟨Z, j, p, _, hj, hp, he⟩ := hi.exists_anodyne_trivialKan_factorization
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := hp
  exact cofinalLlp_of_mono_trivialKan_factorization _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions i j p hj he

/-- 概要：right cofinal な単射は right anodyne。
方針：anodyne と trivial Kan の因子分解から左持ち上げ性を戻す。
規約：単射性が必要。
使われ方：Kerodon Proposition 7.2.1.3（Tag 02N3） の必要性。 -/
lemma IsRightCofinal.rightAnodyneExtensions {X Y : SSet.{u}} {i : X ⟶ Y} [Mono i]
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal i) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i := by
  obtain ⟨Z, j, p, _, hj, hp, he⟩ := hi.exists_anodyne_trivialKan_factorization
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := hp
  exact cofinalLlp_of_mono_trivialKan_factorization _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions i j p hj he

/-- 概要：単射の left cofinality と left anodyne 性は同値。
方針：anodyne の十分性と cofinal な単射の必要性を合わせる。
規約：始域・終域は任意。
使われ方：Kerodon Proposition 7.2.1.3（Tag 02N3）。 -/
@[kerodon 02N3]
lemma isLeftCofinal_iff_leftAnodyne_of_mono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal i ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i :=
  ⟨IsLeftCofinal.leftAnodyneExtensions, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_leftAnodyne i⟩

/-- 概要：単射の right cofinality と right anodyne 性は同値。
方針：anodyne の十分性と cofinal な単射の必要性を合わせる。
規約：始域・終域は任意。
使われ方：Kerodon Proposition 7.2.1.3（Tag 02N3）。 -/
lemma isRightCofinal_iff_rightAnodyne_of_mono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal i ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i :=
  ⟨IsRightCofinal.rightAnodyneExtensions, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne i⟩

/-- 概要：left anodyne な射は単射。
方針：小対象論法の左セル閉包の単射性を既存のホーンの性質に同定する。
規約：cofinality の仮定を加えない。
使われ方：Kerodon Proposition 7.2.1.3（Tag 02N3） の単射性。 -/
lemma cofinalMono_of_leftAnodyne {X Y : SSet.{u}} {i : X ⟶ Y}
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) : Mono i := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalLeftHornFamily_llp_rlp_le_monomorphisms i
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalLeftHornFamily_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions] using hi

/-- 概要：left anodyne 性は単射性と left cofinality の組に一致する。
方針：anodyne な射の単射性・十分性と、cofinal な単射の必要性を合わせる。
規約：単射性を暗黙の仮定にせず右辺に明記する。
使われ方：Kerodon Proposition 7.2.1.3（Tag 02N3）。 -/
@[kerodon 02N3]
lemma leftAnodyneExtensions_iff_mono_and_isLeftCofinal
    {X Y : SSet.{u}} (i : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i ↔ Mono i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal i := by
  constructor
  · intro hi
    exact ⟨cofinalMono_of_leftAnodyne hi, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_leftAnodyne i hi⟩
  · rintro ⟨hm, hi⟩
    have : Mono i := hm
    exact hi.leftAnodyneExtensions

/-- 概要：right anodyne な射は単射。
方針：小対象論法の左セル閉包の単射性を既存のホーンの性質に同定する。
規約：cofinality の仮定を加えない。
使われ方：Kerodon Proposition 7.2.1.3（Tag 02N3） の単射性。 -/
lemma cofinalMono_of_rightAnodyne {X Y : SSet.{u}} {i : X ⟶ Y}
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i) : Mono i := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalRightHornFamily_llp_rlp_le_monomorphisms i
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalRightHornFamily_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions] using hi

/-- 概要：right anodyne 性は単射性と right cofinality の組に一致する。
方針：anodyne な射の単射性・十分性と、cofinal な単射の必要性を合わせる。
規約：単射性を暗黙の仮定にせず右辺に明記する。
使われ方：Kerodon Proposition 7.2.1.3（Tag 02N3）。 -/
@[kerodon 02N3]
lemma rightAnodyneExtensions_iff_mono_and_isRightCofinal
    {X Y : SSet.{u}} (i : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i ↔ Mono i ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal i := by
  constructor
  · intro hi
    exact ⟨cofinalMono_of_rightAnodyne hi, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne i hi⟩
  · rintro ⟨hm, hi⟩
    have : Mono i := hm
    exact hi.rightAnodyneExtensions

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
