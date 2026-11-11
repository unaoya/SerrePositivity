module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinLocalCone
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceTriangleFiber

/-!
概要：変動する固定図式の制限と、Kan 拡張の相対 join 上の局所表示の両立。
方針：slice の制限を引き戻しへ持ち上げ、普遍図式の uncurry を比較する。
規約：固定図式の形は任意。大域的な Kan 拡張の存在・普遍性はここでは主張しない。
使われ方：Kerodon Proposition 7.3.6.7（Tag 030F） の境界と単体の局所問題を比較する。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：固定図式を制限しても slice の可変頂点は変わらない。
方針：普遍図式の uncurry と join の左包含を比較する。
規約：元の図式と制限射は任意。
使われ方：左 Kan の局所形の制限射を引き戻しへ持ち上げる。 -/
lemma kanSliceOverRestrict_projection {L₀ L C : SSet.{u}} (p : L ⟶ C) (f : L₀ ⟶ L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (f ≫ p) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p f)
  have hu := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_restrict (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) f
  simp only [Category.id_comp] at hu
  rw [hu, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection, Category.id_comp] at h
  exact h.symm

/-- 概要：固定図式の制限が左 Kan の局所形に誘導する射。
方針：slice の制限と K 上の恒等射を引き戻しへ持ち上げる。
規約：固定図式 p は点に限らない。
使われ方：単体の全ての面・退化に沿う局所表示の比較。 -/
def kanSliceOverShapeRestrict {K L₀ L C : SSet.{u}}
    (δ : K ⟶ C) (p : L ⟶ C) (f : L₀ ⟶ L) :
    pullback δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) ⟶ pullback δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (f ≫ p)) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p f) (by
    rw [Category.assoc, kanSliceOverRestrict_projection, pullback.condition])

/-- 概要：左局所形の制限は K への射影を保つ。
方針：引き戻しの第一射影の計算則。
規約：厳密な射の等式。
使われ方：制限前後の係数図式の同定。 -/
lemma kanSliceOverShapeRestrict_fst {K L₀ L C : SSet.{u}}
    (δ : K ⟶ C) (p : L ⟶ C) (f : L₀ ⟶ L) :
    kanSliceOverShapeRestrict δ p f ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- 概要：左局所形の制限の slice 成分は通常の slice の制限。
方針：引き戻しの第二射影の計算則。
規約：厳密な射の等式。
使われ方：普遍余錐の uncurry の比較。 -/
lemma kanSliceOverShapeRestrict_snd {K L₀ L C : SSet.{u}}
    (δ : K ⟶ C) (p : L ⟶ C) (f : L₀ ⟶ L) :
    kanSliceOverShapeRestrict δ p f ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p f := pullback.lift_snd _ _ _

/-- 概要：固定図式の制限が右 Kan の局所形に誘導する射。
方針：coslice の制限と K 上の恒等射を引き戻しへ持ち上げる。
規約：左の因子が固定図式、右の因子が K。
使われ方：右 Kan の局所問題を面・退化に沿って比較する。 -/
def kanSliceUnderShapeRestrict {K L₀ L C : SSet.{u}}
    (δ : K ⟶ C) (p : L ⟶ C) (f : L₀ ⟶ L) :
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) δ ⟶ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ p)) δ :=
  pullback.lift (pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p f) (pullback.snd _ _) (by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection, pullback.condition])

/-- 概要：右局所形の制限の coslice 成分。
方針：引き戻しの第一射影の計算則。
規約：厳密な射の等式。
使われ方：普遍錐の uncurry の比較。 -/
lemma kanSliceUnderShapeRestrict_fst {K L₀ L C : SSet.{u}}
    (δ : K ⟶ C) (p : L ⟶ C) (f : L₀ ⟶ L) :
    kanSliceUnderShapeRestrict δ p f ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p f := pullback.lift_fst _ _ _

/-- 概要：右局所形の制限は K への射影を保つ。
方針：引き戻しの第二射影の計算則。
規約：厳密な射の等式。
使われ方：制限前後の係数図式の同定。 -/
lemma kanSliceUnderShapeRestrict_snd {K L₀ L C : SSet.{u}}
    (δ : K ⟶ C) (p : L ⟶ C) (f : L₀ ⟶ L) :
    kanSliceUnderShapeRestrict δ p f ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- 概要：左局所形の恒等図式による制限は恒等射。
方針：引き戻しの両射影と各 slice 単体の joinMap を計算する。
規約：strict な恒等式。
使われ方：局所形を固定図式に関する反変な図式として扱う。 -/
lemma kanSliceOverShapeRestrict_id {K L C : SSet.{u}} (δ : K ⟶ C) (p : L ⟶ C) :
    kanSliceOverShapeRestrict δ p (𝟙 L) = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [kanSliceOverShapeRestrict, pullback.lift_fst, Category.id_comp]
    rfl
  · have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p (𝟙 L) = 𝟙 _ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro t
      apply Subtype.ext
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (𝟙 _) ≫ t.val = t.val
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]
    simp only [kanSliceOverShapeRestrict, pullback.lift_snd, h,
      Category.id_comp, Category.comp_id]
    rfl

/-- 概要：右局所形の恒等図式による制限は恒等射。
方針：引き戻しの両射影と joinMap の恒等式。
規約：strict な恒等式。
使われ方：右局所形の反変な図式の単位律。 -/
lemma kanSliceUnderShapeRestrict_id {K L C : SSet.{u}} (δ : K ⟶ C) (p : L ⟶ C) :
    kanSliceUnderShapeRestrict δ p (𝟙 L) = 𝟙 _ := by
  apply pullback.hom_ext
  · have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p (𝟙 L) = 𝟙 _ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro t
      apply Subtype.ext
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (𝟙 _) ≫ t.val = t.val
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]
    simp only [kanSliceUnderShapeRestrict, pullback.lift_fst, h,
      Category.id_comp, Category.comp_id]
    rfl
  · simp only [kanSliceUnderShapeRestrict, pullback.lift_snd, Category.id_comp]
    rfl

/-- 概要：左局所形の図式の制限は合成を逆順に保つ。
方針：両射影と joinMap の合成則で比較する。
規約：任意の二つの制限射。
使われ方：局所図式の面・退化の全ての合成関係。 -/
lemma kanSliceOverShapeRestrict_comp {K L₀ L₁ L C : SSet.{u}}
    (δ : K ⟶ C) (p : L ⟶ C) (f : L₀ ⟶ L₁) (g : L₁ ⟶ L) :
    kanSliceOverShapeRestrict δ p (f ≫ g) =
      kanSliceOverShapeRestrict δ p g ≫ kanSliceOverShapeRestrict δ (g ≫ p) f := by
  apply pullback.hom_ext
  · change _ = (kanSliceOverShapeRestrict δ p g ≫
      kanSliceOverShapeRestrict δ (g ≫ p) f) ≫
        pullback.fst δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (f ≫ (g ≫ p)))
    rw [kanSliceOverShapeRestrict_fst, Category.assoc,
      kanSliceOverShapeRestrict_fst, kanSliceOverShapeRestrict_fst]
  · change _ = (kanSliceOverShapeRestrict δ p g ≫
      kanSliceOverShapeRestrict δ (g ≫ p) f) ≫
        pullback.snd δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (f ≫ (g ≫ p)))
    rw [kanSliceOverShapeRestrict_snd,
      Category.assoc (kanSliceOverShapeRestrict δ p g)
        (kanSliceOverShapeRestrict δ (g ≫ p) f) _,
      kanSliceOverShapeRestrict_snd,
      ← Category.assoc (kanSliceOverShapeRestrict δ p g) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (g ≫ p) f),
      kanSliceOverShapeRestrict_snd,
      Category.assoc (pullback.snd δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p g) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (g ≫ p) f)]
    congr 1
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (f ≫ g) ≫ t.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) g ≫ t.val)
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]

/-- 概要：右局所形の図式の制限は合成を逆順に保つ。
方針：両射影と joinMap の合成則を使う。
規約：任意の二つの制限射。
使われ方：右局所図式の面・退化の全ての合成関係。 -/
lemma kanSliceUnderShapeRestrict_comp {K L₀ L₁ L C : SSet.{u}}
    (δ : K ⟶ C) (p : L ⟶ C) (f : L₀ ⟶ L₁) (g : L₁ ⟶ L) :
    kanSliceUnderShapeRestrict δ p (f ≫ g) =
      kanSliceUnderShapeRestrict δ p g ≫ kanSliceUnderShapeRestrict δ (g ≫ p) f := by
  apply pullback.hom_ext
  · change _ = (kanSliceUnderShapeRestrict δ p g ≫
      kanSliceUnderShapeRestrict δ (g ≫ p) f) ≫
        pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (g ≫ p))) δ
    rw [kanSliceUnderShapeRestrict_fst,
      Category.assoc (kanSliceUnderShapeRestrict δ p g)
        (kanSliceUnderShapeRestrict δ (g ≫ p) f) _,
      kanSliceUnderShapeRestrict_fst,
      ← Category.assoc (kanSliceUnderShapeRestrict δ p g) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (g ≫ p) f),
      kanSliceUnderShapeRestrict_fst,
      Category.assoc (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) δ)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p g) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (g ≫ p) f)]
    congr 1
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (f ≫ g) (𝟙 _) ≫ t.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 _) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g (𝟙 _) ≫ t.val)
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
  · change _ = (kanSliceUnderShapeRestrict δ p g ≫
      kanSliceUnderShapeRestrict δ (g ≫ p) f) ≫
        pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (g ≫ p))) δ
    rw [kanSliceUnderShapeRestrict_snd, Category.assoc,
      kanSliceUnderShapeRestrict_snd, kanSliceUnderShapeRestrict_snd]

/-- 概要：左 Kan の局所相対 join 表示は固定図式の制限と可換。
方針：一般の相対 join 持ち上げの自然性と slice の uncurry の二つの自然性を合わせる。
規約：局所形の変化を実際の単体集合の射で追う。
使われ方：境界上と単体上の局所余錐の貼り合わせ。 -/
lemma kanRelativeJoinSliceOver_restrict {K L₀ L C : SSet.{u}}
    (δ : K ⟶ C) (p : L ⟶ C) (f : L₀ ⟶ L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (kanSliceOverShapeRestrict δ p f) (𝟙 L₀) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinSliceOver δ (f ≫ p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (pullback δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p))) f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinSliceOver δ p := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinSliceOver
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift_precomp]
  simp only [kanSliceOverShapeRestrict_fst, Category.id_comp]
  congr 1
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, kanSliceOverShapeRestrict_snd,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_restrict]

/-- 概要：右 Kan の局所相対 join 表示は固定図式の制限と可換。
方針：相対 join 持ち上げと coslice の uncurry の自然性。
規約：右側の局所形の変化も全次数で追う。
使われ方：境界上と単体上の局所錐の貼り合わせ。 -/
lemma kanRelativeJoinSliceUnder_restrict {K L₀ L C : SSet.{u}}
    (δ : K ⟶ C) (p : L ⟶ C) (f : L₀ ⟶ L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 L₀) (kanSliceUnderShapeRestrict δ p f) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinSliceUnder δ (f ≫ p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 (pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) δ)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinSliceUnder δ p := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinSliceUnder
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift_precomp]
  simp only [kanSliceUnderShapeRestrict_snd, Category.id_comp]
  congr 1
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, kanSliceUnderShapeRestrict_fst,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
