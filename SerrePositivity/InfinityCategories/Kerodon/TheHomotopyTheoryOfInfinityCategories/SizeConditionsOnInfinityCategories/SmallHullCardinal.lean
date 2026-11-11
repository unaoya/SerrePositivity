module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.InnerHornClosureCardinal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallQuasicategoryHull

/-!
概要：既存の小さい単体模型と内ホーン Hull に μ-small な非退化単体の評価を付ける。
方針：次数ごとの Shrink 全単射で濃度を移し、同じ canonical hull を使う。
規約：任意の Hull が小さいとは主張せず、元の構成と包含を保持する。
使われ方：Ind-S (7)、P の μ-small 試験形状を含む quasicategory の供給。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 概要：既存の Shrink 模型も元と同じ μ-small な非退化単体評価を持つ。
方針：各次数の Shrink 逆写像の単射性で移送して可算和を評価する。
規約：μ と二つの単体宇宙は独立。使われ方：閉包から小さい宇宙への濃度移送。 -/
theorem hasCardinalLT_model {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    (hω : Cardinal.aleph0 < μ) (X : SSet.{v}) [∀ d, Small.{w} (X.obj d)]
    (hX : HasCardinalLT X.N μ) : HasCardinalLT (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.model.{w, v} X).N μ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_N_of_obj hμ hω
  intro n
  change HasCardinalLT (Shrink.{w} (X _⦋n⦌)) μ
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_obj_of_N hμ X hX n).of_injective
    (equivShrink.{w} (X _⦋n⦌)).symm (equivShrink.{w} (X _⦋n⦌)).symm.injective

/-- 概要：既存 canonical Hull の対象も μ-small な非退化単体数を持つ。
方針：同じ内ホーン閉包の評価を同じ model へ移す。
規約：Hull の包含・全図式因子化を変更しない。使われ方：既存 hull への濃度保証の追加。 -/
theorem hasCardinalLT_hull_obj {μ : Cardinal.{w}} (hμ : μ.IsRegular)
    (hω : Cardinal.aleph0 < μ) {X : SSet.{max u v}} [Quasicategory X]
    (A : X.Subcomplex) [∀ d, Small.{u} (A.obj d)] (hA : HasCardinalLT A.toSSet.N μ) :
    HasCardinalLT (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hull.{u, v} A).obj.N μ := by
  have (d : SimplexCategoryᵒᵖ) : Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.innerHornClosure A).toSSet.obj d) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.small_innerHornClosure A d
  change HasCardinalLT (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.model.{u, max u v} (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.innerHornClosure A).toSSet).N μ
  exact hasCardinalLT_model hμ hω _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.hasCardinalLT_innerHornClosure hμ hω A hA)

/-- 概要：μ-small な種だけから、既存と同じ包含と因子化を持つ Hull を選ぶ。
方針：濃度評価から各次数の宇宙的 Small を得て、既存 hull を適用する。
規約：追加の Small 仮定を公開型に要求しない。使われ方：P の大宇宙内の小模型の直接構成。 -/
def hullOfCardinalBound {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    {X : SSet.{max u v}} [Quasicategory X] (A : X.Subcomplex)
    (hA : HasCardinalLT A.toSSet.N μ) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.Hull.{u, v} X A := by
  have (d : SimplexCategoryᵒᵖ) : Small.{u} (A.obj d) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_obj_of_N hμ A.toSSet hA d.unop.len).small
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hull A

/-- 概要：濃度から構成した同じ Hull は μ-small な対象を持つ。
方針：既存 canonical hull の濃度評価をそのまま読む。
規約：種・包含・因子化の選択を変更しない。使われ方：μ-small な Hull の存在証拠。 -/
theorem hasCardinalLT_hullOfCardinalBound_obj {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    (hω : Cardinal.aleph0 < μ) {X : SSet.{max u v}} [Quasicategory X] (A : X.Subcomplex)
    (hA : HasCardinalLT A.toSSet.N μ) : HasCardinalLT (hullOfCardinalBound hμ A hA).obj.N μ := by
  have (d : SimplexCategoryᵒᵖ) : Small.{u} (A.obj d) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_obj_of_N hμ A.toSSet hA d.unop.len).small
  have (d : SimplexCategoryᵒᵖ) : Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.innerHornClosure A).toSSet.obj d) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.small_innerHornClosure A d
  change HasCardinalLT (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.model.{u, max u v} (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.innerHornClosure A).toSSet).N μ
  exact hasCardinalLT_model hμ hω _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.hasCardinalLT_innerHornClosure hμ hω A hA)

/-- 概要：μ-small な種を含む μ-small な対象の Hull が存在する。
方針：濃度から得た同じ canonical Hull と評価を対にする。
規約：元の Hull の全図式因子化を含む。使われ方：P の試験形状に対する有界な充填模型。 -/
theorem exists_hull_hasCardinalLT {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    (hω : Cardinal.aleph0 < μ) {X : SSet.{max u v}} [Quasicategory X] (A : X.Subcomplex)
    (hA : HasCardinalLT A.toSSet.N μ) : ∃ H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.Hull.{u, v} X A, HasCardinalLT H.obj.N μ :=
  ⟨hullOfCardinalBound hμ A hA, hasCardinalLT_hullOfCardinalBound_obj hμ hω A hA⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
