module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinDiagonalSplit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinBaseProjection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinIntervalEndpointPullbacks

/-!
概要：slice の普遍余錐を相対 join 上に表示する。
方針：join 上の図式を区間成分と組にし、区間付き対角の引き戻しへ持ち上げる。
規約：元の δ の単射性や quasicategory 性を構成には要求しない。
使われ方：相対 join 上の図式の制限を Kan 拡張の比較余錐に接続する。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：両端が指定した構造射と両立する join の図式を relative join へ持ち上げる。
方針：左右の射の join と、区間付き図式を pullback に入れる。
規約：両端の等式だけを要求する。
使われ方：slice の普遍余錐から相対 join への標準の射。 -/
def kanRelativeJoinLift {A B X Y C : SSet.{u}}
    (f : X ⟶ C) (g : Y ⟶ C) (a : A ⟶ X) (b : B ⟶ Y)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ H = a ≫ f)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ H = b ≫ g) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f g :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap a b) (lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection A B) H) (by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, ← hA, ← hB, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinDiagonal_split_map])

/-- 概要：標準持ち上げを通常の join へ射影すると左右の指定射の join。
方針：pullback の第一射影の計算則。
規約：全ての射を厳密な等式で比較する。
使われ方：相対 join の左端・右端の制限の計算。 -/
lemma kanRelativeJoinLift_fst {A B X Y C : SSet.{u}}
    (f : X ⟶ C) (g : Y ⟶ C) (a : A ⟶ X) (b : B ⟶ Y)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ H = a ≫ f)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ H = b ≫ g) :
    kanRelativeJoinLift f g a b H hA hB ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal C) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap a b := pullback.lift_fst _ _ _

/-- 概要：標準持ち上げの区間付き係数は元の区間と図式の組。
方針：pullback の第二射影の計算則。
規約：区間成分も厳密に保持する。
使われ方：部分図式への制限との自然性。 -/
lemma kanRelativeJoinLift_snd {A B X Y C : SSet.{u}}
    (f : X ⟶ C) (g : Y ⟶ C) (a : A ⟶ X) (b : B ⟶ Y)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ H = a ≫ f)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ H = b ≫ g) :
    kanRelativeJoinLift f g a b H hA hB ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal C) =
      lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection A B) H := pullback.lift_snd _ _ _

/-- 概要：標準持ち上げは左右のパラメータの制限と可換。
方針：第一射影には joinMap の合成則、第二射影には区間射影の自然性を使う。
規約：左右の制限射は任意。
使われ方：slice の普遍図式の高次単体への制限の両立。 -/
lemma kanRelativeJoinLift_precomp {A₀ B₀ A B X Y C : SSet.{u}}
    (f : X ⟶ C) (g : Y ⟶ C) (a : A ⟶ X) (b : B ⟶ Y)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ H = a ≫ f)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ H = b ≫ g) (u : A₀ ⟶ A) (v : B₀ ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap u v ≫ kanRelativeJoinLift f g a b H hA hB =
      kanRelativeJoinLift f g (u ≫ a) (v ≫ b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap u v ≫ H)
        (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, hA, Category.assoc])
        (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc, hB, Category.assoc]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinLift_fst, kanRelativeJoinLift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
  · rw [Category.assoc, kanRelativeJoinLift_snd, kanRelativeJoinLift_snd]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_naturality u v
    · simp only [Category.assoc, lift_snd]

/-- 概要：標準持ち上げの係数の底への射影は元の図式。
方針：pullback の第二射影と直積の第二射影を計算する。
規約：図式 H を全単体で保持する。
使われ方：slice の普遍余錐との厳密な両立。 -/
lemma kanRelativeJoinLift_base {A B X Y C : SSet.{u}}
    (f : X ⟶ C) (g : Y ⟶ C) (a : A ⟶ X) (b : B ⟶ Y)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ H = a ≫ f)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ H = b ≫ g) :
    kanRelativeJoinLift f g a b H hA hB ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection f g = H := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection, ← Category.assoc, kanRelativeJoinLift, pullback.lift_snd,
    lift_snd]

/-- 概要：標準持ち上げの左端は指定した左の射。
方針：pullback の両射影を比較し、区間成分と係数成分を別々に計算する。
規約：単射性を使わない。
使われ方：局所比較余錐の図式部分の厳密な同定。 -/
lemma kanRelativeJoinLift_inl {A B X Y C : SSet.{u}}
    (f : X ⟶ C) (g : Y ⟶ C) (a : A ⟶ X) (b : B ⟶ Y)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ H = a ≫ f)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ H = b ≫ g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ kanRelativeJoinLift f g a b H hA hB = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl f g := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinLift_fst, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl_fst,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap]
  · simp only [kanRelativeJoinLift, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl, Category.assoc, pullback.lift_snd]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, SSet.comp_const]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_inl A B
    · simp only [Category.assoc, lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, Category.comp_id]
      exact hA

/-- 概要：標準持ち上げの右端は指定した右の射。
方針：pullback の二成分と区間の一端を計算する。
規約：両端を同じ持ち上げで固定する。
使われ方：局所比較余錐の頂点の同定。 -/
lemma kanRelativeJoinLift_inr {A B X Y C : SSet.{u}}
    (f : X ⟶ C) (g : Y ⟶ C) (a : A ⟶ X) (b : B ⟶ Y)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ H = a ≫ f)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ H = b ≫ g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ kanRelativeJoinLift f g a b H hA hB = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr f g := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinLift_fst, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_fst,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap]
  · simp only [kanRelativeJoinLift, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr, Category.assoc, pullback.lift_snd]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, SSet.comp_const]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_inr A B
    · simp only [Category.assoc, lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, Category.comp_id]
      exact hB

/-- 概要：任意の固定図式 p に対する slice の普遍図式を相対 join へ写す。
方針：sliceOver の uncurry と引き戻しの可換条件を標準持ち上げへ入れる。
規約：固定因子 L は点に限らない。
使われ方：高次単体を含む slice の比較を同じ構成で扱う。 -/
def kanRelativeJoinSliceOver {K L C : SSet.{u}} (δ : K ⟶ C) (p : L ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (pullback δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)) L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin δ (𝟙 C) :=
  kanRelativeJoinLift δ (𝟙 C) (pullback.fst δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)) p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (pullback.snd δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)))
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection, ← pullback.condition])
    (by simpa only [Category.comp_id] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed (pullback.snd δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)))

/-- 概要：任意の固定図式 p に対する coslice の普遍図式を相対 join へ写す。
方針：sliceUnder の uncurry と引き戻しの可換条件を標準持ち上げへ入れる。
規約：固定因子 L は任意の単体集合。
使われ方：右 Kan の高次単体を含む比較。 -/
def kanRelativeJoinSliceUnder {K L C : SSet.{u}} (δ : K ⟶ C) (p : L ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join L (pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) δ) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ :=
  kanRelativeJoinLift (𝟙 C) δ p (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) δ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) δ))
    (by simpa only [Category.comp_id] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) δ))
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection, pullback.condition])

/-- 概要：左 Kan の slice の普遍余錐を相対 join へ写す標準の射。
方針：左因子を K への射影、右因子を c とし、普遍余錐を係数とする。
規約：δ は任意。
使われ方：相対 join 表示から点 c での比較余錐を読む。 -/
def kanRelativeJoinLocalCocone {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin δ (𝟙 C) :=
  kanRelativeJoinSliceOver δ (SSet.yonedaEquiv.symm c)

/-- 概要：局所余錐の図式部分は K の相対 join への包含。
方針：一般の持ち上げの左端の計算則を適用する。
規約：図式の制限は厳密な等式。
使われ方：相対 join の図式から局所比較余錐を構成する。 -/
lemma kanRelativeJoinLocalCocone_inl {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u}) ≫ kanRelativeJoinLocalCocone δ c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl δ (𝟙 C) := by
  unfold kanRelativeJoinLocalCocone kanRelativeJoinSliceOver
  apply kanRelativeJoinLift_inl

/-- 概要：局所余錐の頂点は c の相対 join の右端への包含。
方針：一般の持ち上げの右端の計算則。
規約：頂点を別途選ばない。
使われ方：局所比較余錐の値の同定。 -/
lemma kanRelativeJoinLocalCocone_inr {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u}) ≫ kanRelativeJoinLocalCocone δ c =
      SSet.yonedaEquiv.symm c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr δ (𝟙 C) := by
  unfold kanRelativeJoinLocalCocone kanRelativeJoinSliceOver
  apply kanRelativeJoinLift_inr

/-- 概要：相対 join 上の図式を c の slice に制限して余錐にする。
方針：局所余錐の標準射に図式を後合成する。
規約：元の左端の図式の slice 制限上の余錐。
使われ方：相対 join 表示と点ごとの左 Kan 条件の比較。 -/
def kanRelativeJoinDiagramCocone {K C D : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin δ (𝟙 C) ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl δ (𝟙 C) ≫ G) :=
  ⟨kanRelativeJoinLocalCocone δ c ≫ G, by
    rw [← Category.assoc, kanRelativeJoinLocalCocone_inl, Category.assoc]⟩

/-- 概要：相対 join の図式から得た局所余錐の頂点。
方針：右端の計算を Yoneda 対応で評価する。
規約：G の右端の c での値。
使われ方：左 Kan の点ごとの値との照合。 -/
lemma kanRelativeJoinDiagramCocone_vertex {K C D : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin δ (𝟙 C) ⟶ D) :
    (kanRelativeJoinDiagramCocone δ c G).vertex =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr δ (𝟙 C) ≫ G).app (Opposite.op ⦋0⦌) c := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ (kanRelativeJoinLocalCocone δ c ≫ G)) = _
  rw [← Category.assoc, kanRelativeJoinLocalCocone_inr, Category.assoc,
    SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- 概要：右 Kan の coslice の普遍錐を相対 join へ写す標準射。
方針：左因子を c、右因子を K への射影とし、普遍錐を係数とする。
規約：右 Kan では相対 join の因子の順を C、K とする。
使われ方：右指定変換に対する点ごとの比較錐の表示。 -/
def kanRelativeJoinLocalCone {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape δ c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ :=
  kanRelativeJoinSliceUnder δ (SSet.yonedaEquiv.symm c)

/-- 概要：局所錐の頂点は c の相対 join の左端への包含。
方針：一般の持ち上げの左端の計算則。
規約：δ は任意。
使われ方：右比較錐の頂点の同定。 -/
lemma kanRelativeJoinLocalCone_inl {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape δ c) ≫ kanRelativeJoinLocalCone δ c =
      SSet.yonedaEquiv.symm c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ := by
  unfold kanRelativeJoinLocalCone kanRelativeJoinSliceUnder
  apply kanRelativeJoinLift_inl

/-- 概要：局所錐の図式部分は K の相対 join への包含。
方針：一般の持ち上げの右端の計算則。
規約：頂点部分と同じ持ち上げから得る。
使われ方：右比較錐の制限図式の同定。 -/
lemma kanRelativeJoinLocalCone_inr {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanShape δ c) ≫ kanRelativeJoinLocalCone δ c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (𝟙 C) δ := by
  unfold kanRelativeJoinLocalCone kanRelativeJoinSliceUnder
  apply kanRelativeJoinLift_inr

/-- 概要：相対 join 上の図式を c の coslice に制限して錐にする。
方針：局所錐の標準射に図式を後合成する。
規約：元の右端の図式の coslice 制限上の錐。
使われ方：相対 join 表示と点ごとの右 Kan 条件の比較。 -/
def kanRelativeJoinDiagramCone {K C D : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (𝟙 C) δ ≫ G) :=
  ⟨kanRelativeJoinLocalCone δ c ≫ G, by
    rw [← Category.assoc, kanRelativeJoinLocalCone_inr, Category.assoc]⟩

/-- 概要：相対 join の図式から得た局所錐の頂点。
方針：左端の計算を Yoneda 対応で評価する。
規約：G の左端の c での値。
使われ方：右 Kan の点ごとの値との照合。 -/
lemma kanRelativeJoinDiagramCone_vertex {K C D : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ ⟶ D) :
    (kanRelativeJoinDiagramCone δ c G).vertex =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ ≫ G).app (Opposite.op ⦋0⦌) c := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ (kanRelativeJoinLocalCone δ c ≫ G)) = _
  rw [← Category.assoc, kanRelativeJoinLocalCone_inl, Category.assoc,
    SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- 概要：slice の標準持ち上げを底へ射影すると元の普遍図式が得られる。
方針：一般の持ち上げの係数射影の計算則。
規約：固定図式 p を全単体で保つ。
使われ方：相対 join の局所制限と元の slice の照合。 -/
lemma kanRelativeJoinSliceOver_base {K L C : SSet.{u}} (δ : K ⟶ C) (p : L ⟶ C) :
    kanRelativeJoinSliceOver δ p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection δ (𝟙 C) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (pullback.snd δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)) :=
  kanRelativeJoinLift_base _ _ _ _ _ _ _

/-- 概要：coslice の標準持ち上げを底へ射影すると元の普遍図式が得られる。
方針：一般の持ち上げの係数射影の計算則。
規約：固定図式 p は任意。
使われ方：右比較錐の底との両立。 -/
lemma kanRelativeJoinSliceUnder_base {K L C : SSet.{u}} (δ : K ⟶ C) (p : L ⟶ C) :
    kanRelativeJoinSliceUnder δ p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection (𝟙 C) δ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) δ) :=
  kanRelativeJoinLift_base _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
