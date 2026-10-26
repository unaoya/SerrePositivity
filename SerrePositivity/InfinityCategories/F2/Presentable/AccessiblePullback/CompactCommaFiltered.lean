module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.CompactInputSliceCocones
public import SerrePositivity.InfinityCategories.F2.Presentable.CompactSourcePullbackModels
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallTestFilteredModels

/-!
概要：compact 入力の全余錐を compact comma の小さい filtered 模型へ接続する。
方針：小さい quasicategory 試験から全試験へ移し、既存の全同値模型へ戻す。
規約：生成表示の余極限性は別に証明する。
使われ方：一般 accessible 引き戻しの生成表示の添字。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
open HomotopyLimits

/-- 概要：小さい compact 成分 slice 入力を compact 成分の全余錐へ延長する条件。
方針：元の引き戻しと全入力図式をそのまま量化する。
規約：accessible 性や全同値の存在をこの条件に隠さない。
使われ方：実際の交互構成の出力から filtered 模型への接続。 -/
def HasCompactSliceCocones (μ : Cardinal.{u})
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) : Prop :=
  ∀ (K : SSet.{u}) (hK : Quasicategory K), letI := hK
    IsKappaSmall μ K → ∀ (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q)
      (U : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceOver x),
      (∀ v, ComponentCompactVertex μ p q
        ((U ≫ sliceOverProjection x).app (Opposite.op ⦋0⦌) v)) →
      ∃ c : JoinCocone U, ComponentCompactVertex μ p q
        ((sliceOverProjection x).app (Opposite.op ⦋0⦌) c.vertex)

/-- 概要：元の accessible 成分の相対交互構成は全 compact 入力余錐条件を満たす。
方針：同じ濃度と元の全入力について実際の構成を適用する。
規約：追加の生成性や同値の存在を仮定しない。
使われ方：一般引き戻しの小さい filtered comma 模型への無条件接続。 -/
lemma hasCompactSliceCocones_of_accessible_components
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : F1B.EquivalenceLifting p)
    (hE : IsKappaAccessible μ E) (hD : IsKappaAccessible μ D)
    (hB : IsKappaAccessible μ B)
    (hEκ : Ind.HasSmallKappaFilteredColimits κ E)
    (hDκ : Ind.HasSmallKappaFilteredColimits κ D)
    (hBκ : Ind.HasSmallKappaFilteredColimits κ B)
    (hpμ : IsKappaAccessibleFunctor μ p) (hqμ : IsKappaAccessibleFunctor μ q)
    (hpκ : IsKappaAccessibleFunctor κ p) (hqκ : IsKappaAccessibleFunctor κ q)
    (hpCompact : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ v →
      Compact.IsKappaCompact.{u, u + 1} μ (p.app (Opposite.op ⦋0⦌) v))
    (hqCompact : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ v →
      Compact.IsKappaCompact.{u, u + 1} μ (q.app (Opposite.op ⦋0⦌) v)) :
    HasCompactSliceCocones μ p q := by
  intro K hK hsmall x U hU
  letI := hK
  exact exists_componentCompactSliceCocone_of_accessible_components h hsmall p q hp
    hE hD hB hEκ hDκ hBκ hpμ hqμ hpκ hqκ hpCompact hqCompact x U hU

/-- 概要：compact 入力の余錐から compact comma の任意の小さい試験余錐を得る。
方針：小さい quasicategory への有界因子化と全部分圏への全余錐持ち上げを使う。
規約：任意の小さい試験形状を扱い、quasicategory 形状だけで filtered としない。
使われ方：compact comma の小模型の filtered 判定。 -/
lemma nonempty_componentCompactOver_cocone_of_compactSliceCocones
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : F1B.EquivalenceLifting p)
    (hcone : HasCompactSliceCocones μ p q)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q)
    (K : SSet.{u}) (hK : IsKappaSmall μ K)
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ componentCompactOver μ p q x) :
    Nonempty (JoinCocone r) := by
  letI := hp.innerFibration
  apply nonempty_cocone_of_smallQuasicategory_tests hμ ?_ K hK r
  intro L hL hsmall j
  let P := fun v : (sliceOver x) _⦋0⦌ ↦
    ComponentCompactVertex μ p q ((sliceOverProjection x).app (Opposite.op ⦋0⦌) v)
  let i := (fullSubcomplexOnVertices (sliceOver x) P).ι
  obtain ⟨c, hc⟩ := hcone L hL hsmall x (j ≫ i)
    (fun v ↦ fullSubcomplexOnVertices_vertex (j.app (Opposite.op ⦋0⦌) v))
  exact ⟨fullSubcomplexCoconeLift P j c hc⟩

/-- 概要：compact 入力の余錐と accessible 成分から compact comma の小さい filtered 模型を得る。
方針：既存の小さい全同値模型へ全小試験余錐を移す。
規約：元の濃度を保ち、標準余錐の余極限性はまだ要求しない。
使われ方：元の各対象の小さい compact 成分生成表示の添字。 -/
lemma exists_smallKappaFilteredComponentCommaModel_of_compactSliceCocones
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : F1B.EquivalenceLifting p)
    (hE : IsKappaAccessible μ E) (hD : IsKappaAccessible μ D) (hB : IsKappaAccessible μ B)
    (hpCompact : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ v →
      Compact.IsKappaCompact.{u, u + 1} μ (p.app (Opposite.op ⦋0⦌) v))
    (hqCompact : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ v →
      Compact.IsKappaCompact.{u, u + 1} μ (q.app (Opposite.op ⦋0⦌) v))
    (hcone : HasCompactSliceCocones μ p q)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q) :
    letI := hp.innerFibration
    ∃ (M : SSet.{u}) (hM : Quasicategory M), letI := hM
      IsKappaFiltered μ M ∧ Nonempty (QCatEquivalence
        ((SSet.uliftFunctor.{u + 1, u}).obj M) (componentCompactOver μ p q x)) := by
  letI := hp.innerFibration
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_smallComponentCompactOverModel p q hp hE hD hB
    hpCompact hqCompact x
  letI := hM
  refine ⟨M, hM, ?_, ⟨e⟩⟩
  exact isKappaFiltered_of_small_tests_equivalence e (fun K hK r ↦
    nonempty_componentCompactOver_cocone_of_compactSliceCocones hμ p q hp hcone x K hK r)

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
