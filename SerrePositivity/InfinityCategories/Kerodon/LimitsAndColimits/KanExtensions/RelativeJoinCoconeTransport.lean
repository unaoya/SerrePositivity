module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinShiftPrism
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.ComparisonCartesian

/-!
概要：相対 join の局所余錐を指定自然変換の比較余錐として表示する。
方針：持ち上げた prism を図式で写し、四境界を輸送のフィールドへ渡す。
規約：輸送の存在を追加仮定せず、実際の族を構成する。
使われ方：相対 join 上の左 Kan 条件と点ごとの局所余極限性の比較。

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

/-- 概要：相対 join 上の図式の標準 prism が与える指定自然変換。
方針：時間を第二因子へ直し、両端の計算則を使う。
規約：変換の向きは左端から右端の δ に沿う制限。
使われ方：局所比較余錐の指定変換。 -/
def kanRelativeJoinTransformation {K C D : SSet.{u}} (δ : K ⟶ C)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin δ (𝟙 C) ⟶ D) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl δ (𝟙 C) ≫ G) (δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr δ (𝟙 C) ≫ G) where
  h := (β_ K (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism δ ≫ G
  h₀ := by
    rw [← Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism δ ≫ G = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_zero]
    rfl
  h₁ := by
    rw [← Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism δ ≫ G = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_one, Category.assoc]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：相対 join の局所余錐から、指定変換に両立する実際の輸送を構成する。
方針：slice の普遍余錐の移動 prism に G を後合成し、四境界を計算する。
規約：D の quasicategory 性を構成には要求しない。
使われ方：局所余錐の余極限性を左 Kan 条件へ移す。 -/
def kanRelativeJoinCoconeTransport {K C D : SSet.{u}} (δ : K ⟶ C)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin δ (𝟙 C) ⟶ D) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanCoconeTransport δ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl δ (𝟙 C) ≫ G)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr δ (𝟙 C) ≫ G) (kanRelativeJoinTransformation δ G) c where
  family := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinShiftPrism δ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (pullback.snd δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c))))
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection, ← pullback.condition]) ≫ G
  finish := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinShiftPrism_one]
    rfl
  diagram := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinShiftPrism_left]
    have h : (β_ (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c)).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c ▷ (Δ[1] : SSet.{u})) ≫
        (β_ K (Δ[1] : SSet.{u})).hom = ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c) := rfl
    simpa only [kanRelativeJoinTransformation, Category.assoc] using
      (congrArg (fun q ↦ q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism δ ≫ G) h).symm
  fixedVertex := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinShiftPrism_right]
    rfl

/-- 概要：構成した輸送の比較余錐は、元の相対 join の局所余錐と同じ射を持つ。
方針：移動 prism の始点を計算し、slice の固定端の式を使う。
規約：添字図式の表示の違いを避けて raw な射の等式で述べる。
使われ方：余極限性を両表示の間で移す。 -/
lemma kanRelativeJoinCoconeTransport_cocone_val {K C D : SSet.{u}} (δ : K ⟶ C)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin δ (𝟙 C) ⟶ D) (c : C _⦋0⦌) :
    (kanRelativeJoinCoconeTransport δ G c).cocone.val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinDiagramCocone δ c G).val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinShiftPrism δ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (pullback.snd δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c)))) _ ≫ G) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinShiftPrism_zero]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed]
  rfl

/-- 概要：構成した輸送の比較余錐は相対 join の局所余錐に等しい。
方針：raw な射の同一性から部分型の外延性を使う。
規約：添字図式の定義を展開した同じ部分型で比較する。
使われ方：左 Kan 条件と局所余極限性の同値。 -/
lemma kanRelativeJoinCoconeTransport_cocone {K C D : SSet.{u}} (δ : K ⟶ C)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin δ (𝟙 C) ⟶ D) (c : C _⦋0⦌) :
    (kanRelativeJoinCoconeTransport δ G c).cocone = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinDiagramCocone δ c G :=
  Subtype.ext (kanRelativeJoinCoconeTransport_cocone_val δ G c)

/-- 概要：相対 join の標準指定変換の左 Kan 条件は局所余錐の余極限性と同値。
方針：実際の局所輸送と、比較余錐の選択不変性を合わせる。
規約：D の quasicategory 性を使うが δ の単射性は不要。
使われ方：点ごとの定義を相対 join 上の図式の制限として扱う。 -/
lemma isLeftKanExtension_relativeJoin_iff_local_colimits {K C D : SSet.{u}}
    [Quasicategory D] (δ : K ⟶ C) (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin δ (𝟙 C) ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension δ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl δ (𝟙 C) ≫ G) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr δ (𝟙 C) ≫ G)
      (kanRelativeJoinTransformation δ G) ↔
      ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinDiagramCocone δ c G) := by
  constructor
  · intro h c
    have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isLeftKanExtension_iff_forall_transport δ _ _ _).1 h c
      (kanRelativeJoinCoconeTransport δ G c)
    rwa [kanRelativeJoinCoconeTransport_cocone] at ht
  · intro h c
    refine ⟨kanRelativeJoinCoconeTransport δ G c, ?_⟩
    rw [kanRelativeJoinCoconeTransport_cocone]
    exact h c

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
