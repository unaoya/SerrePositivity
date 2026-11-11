module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PredicateOverCocones
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComponentCompactQuasicategoryColimits

/-!
概要：compact 成分を持つ対象上の comma に、小さい quasicategory 図式の余錐を与える。
方針：引き戻しの指定余極限の compact 閉性を対象上の内部余錐へ移す。
規約：試験形状の quasicategory 性を明示し、一般形状での filtered 性と混同しない。
使われ方：小さい compact 生成候補による filtered 表示の添字の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：固定対象への射を持ち、始域の両成分が compact な全部分圏。
方針：元の slice の頂点に同じ成分 compact 条件を課す。
規約：元の射と全高次単体を保持する。
使われ方：compact 生成表示の元の comma 模型。 -/
def componentCompactOver (μ : Cardinal.{u})
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q) :
    SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x)
    (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app _ v))

instance componentCompactOver_quasicategory (μ : Cardinal.{u})
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p]
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q) :
    Quasicategory (componentCompactOver μ p q x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- 概要：対象上の compact 成分の μ-small quasicategory 図式は内部の余錐を持つ。
方針：底の元の余極限を取り、その compact 閉性を対象上で保つ。
規約：ここでは試験形状が quasicategory の場合のみを結論する。
使われ方：一般試験形状を小さい充填閉包で置き換えた後の余錐構成。 -/
lemma nonempty_componentCompactOver_cocone_of_smallQuasicategory
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    (K : SSet.{u}) [Quasicategory K] (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K)
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits E) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits D)
    (hpc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p) (hqc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits q)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q)
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ componentCompactOver μ p q x) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r) := by
  have : InnerFibration p := hp.innerFibration
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q
  let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x)
    (fun v ↦ P ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app _ v))).ι
  let F := (r ≫ j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_hasSmallColimits p q hp hE hD hpc hqc K F
  have hF : ∀ i, P (F.app (Opposite.op ⦋0⦌) i) := by
    intro i
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (r.app (Opposite.op ⦋0⦌) i)
  have hP : P c.vertex :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.componentCompactVertex_smallQuasicategoryColimit_of_span hμ K hK p q hp
      hE hD hpc hqc c hc hF
  obtain ⟨d, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_predicateOver_cocone_lifting_colimit P x r c hc hP
  exact ⟨d⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
