module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PointSlicePostcomp
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes

/-!
概要：厳密に可換な二関手の正方形が誘導する、同じ指定頂点の comma の作用。
方針：始域と全錐を同時に写し、正規化した点 slice の後合成を使う。
規約：全変換の射を厳密に回収。使われ方：全図式 comma の各頂点での評価。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {A B X Y : SSet.{u}} (δ : A ⟶ X) (ε : B ⟶ Y)
  (f : A ⟶ B) (g : X ⟶ Y) (h : δ ≫ g = f ≫ ε) (x : X _⦋0⦌)

/-- 同じ始点図式と元の全変換を可換正方形で同時に写す。 -/
def commaPostcomp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape ε (g.app (Opposite.op ⦋0⦌) x) :=
  pullback.lift (pullback.fst _ _ ≫ f) (pullback.snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSlicePostcomp g x) (by
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSlicePostcomp_projection, ← h, ← Category.assoc, pullback.condition, Category.assoc])

/-- 元の始点図式への射影は正方形の始域作用そのもの。 -/
lemma commaPostcomp_projection : commaPostcomp δ ε f g h x ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection ε (g.app (Opposite.op ⦋0⦌) x) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ x ≫ f :=
  pullback.lift_fst _ _ _

/-- 元の全パラメータの全錐は、同じ全錐の後合成そのものへ送られる。 -/
lemma commaPostcomp_uncurry {T : SSet.{u}} (q : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (q ≫ commaPostcomp δ ε f g h x ≫
      pullback.snd ε (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm
        (g.app (Opposite.op ⦋0⦌) x)))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (q ≫ pullback.snd δ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x))) ≫ g := by
  simp only [commaPostcomp, Category.assoc, pullback.lift_snd]
  simpa only [Category.assoc] using _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.pointSlicePostcomp_uncurry g x
    (q ≫ pullback.snd δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x)))

/-- comma の終点表示の等式による移送は、元の全錐の射を変えない。 -/
lemma commaTransport_uncurry {T : SSet.{u}} {v w : X _⦋0⦌} (hv : v = w)
    (q : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (q ≫ eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ) hv) ≫
      pullback.snd δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm w))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (q ≫ pullback.snd δ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm v))) := by
  cases hv
  simp only [eqToHom_refl, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
