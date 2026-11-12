module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallInnerHornClosure
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SimplicialCardinalBounds
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：元の内ホーン充填閉包が正則非可算濃度未満であることを示す。
方針：有限個の面でホーン写像を数え、各段の次数別評価を可算和で閉じる。
規約：既存の閉包と充填選択を変更せず、F2 の述語を import しない。
使われ方：Ind-S (7)、P の μ-small 試験形状を含む小さい quasicategory の供給。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：ホーン写像の全族は有限個の面の値で評価できる。
方針：各面への制限の Yoneda 値への単射を作る。
規約：標的の充填性は不要。使われ方：一段で追加する充填単体の添字の評価。 -/
lemma hasCardinalLT_horn_hom {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
    (A : SSet.{v}) (n : ℕ) (i : Fin (n + 3))
    (hA : HasCardinalLT (A _⦋n + 1⦌) μ) :
    HasCardinalLT ((Λ[n + 2, i] : SSet.{v}) ⟶ A) μ := by
  let f : ((Λ[n + 2, i] : SSet.{v}) ⟶ A) →
      ({j : Fin (n + 3) // j ≠ i} → A _⦋n + 1⦌) :=
    fun a j => SSet.yonedaEquiv (horn.ι i j.val j.property ≫ a)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_finite_arrow hμ hA _).of_injective f
  intro a b hab
  apply horn.hom_ext'
  intro j hj
  apply SSet.yonedaEquiv.injective
  exact congrFun hab ⟨j, hj⟩

/-- 概要：各次数が μ 未満なら、全内ホーン試験族も μ 未満。
方針：次元の可算和と内面の有限和を正則性で評価する。
規約：可算関数空間は作らない。使われ方：元の innerHornStep の充填添字の評価。 -/
lemma hasCardinalLT_innerHornData {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    (hω : Cardinal.aleph0 < μ) (A : SSet.{v})
    (hA : ∀ n : ℕ, HasCardinalLT (A _⦋n⦌) μ) : HasCardinalLT (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.InnerHornData A) μ := by
  letI : Fact μ.IsRegular := ⟨hμ⟩
  apply hasCardinalLT_sigma _ μ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_nat hω)
  intro n
  apply hasCardinalLT_sigma _ μ (hasCardinalLT_of_finite _ μ hμ.aleph0_le)
  intro i
  exact hasCardinalLT_horn_hom hμ.aleph0_le A n i.val (hA (n + 1))

/-- 概要：μ 個未満の部分複体の和の指定次数も μ 未満。
方針：同じ次数の集合の和を正則濃度の和として評価する。
規約：非退化単体の移送は使わない。使われ方：選択充填族と可算段階の共通評価。 -/
lemma hasCardinalLT_iSup_obj {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    {X : SSet.{v}} {I : Type w} (hI : HasCardinalLT I μ)
    (A : I → X.Subcomplex) (d : SimplexCategoryᵒᵖ)
    (hA : ∀ i, HasCardinalLT ((A i).obj d) μ) : HasCardinalLT ((⨆ i, A i).obj d) μ := by
  letI : Fact μ.IsRegular := ⟨hμ⟩
  simp only [Subfunctor.iSup_obj]
  exact hasCardinalLT_iUnion _ hI hA

/-- 概要：一段の内ホーン充填は指定次数の濃度を μ 未満に保つ。
方針：充填の添字を面の有限積で数え、各標準単体の像の有限性を使う。
規約：元の充填選択の像だけを数える。使われ方：innerHornStage の帰納段階。 -/
lemma hasCardinalLT_innerHornStep_obj {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    (hω : Cardinal.aleph0 < μ) {X : SSet.{v}} [Quasicategory X] (A : X.Subcomplex)
    (hA : ∀ n : ℕ, HasCardinalLT (A.toSSet _⦋n⦌) μ) (n : ℕ) :
    HasCardinalLT ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.innerHornStep A).toSSet _⦋n⦌) μ := by
  have hI := hasCardinalLT_innerHornData hμ hω A.toSSet hA
  have hF (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.InnerHornData A.toSSet) :
      HasCardinalLT ((SSet.Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.innerHornFiller A h)).obj (Opposite.op ⦋n⦌)) μ := by
    let f : (Δ[h.1 + 2] : SSet.{v}) _⦋n⦌ → X _⦋n⦌ :=
      fun s => (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.innerHornFiller A h).app (Opposite.op ⦋n⦌) s
    change HasCardinalLT (Set.range f) μ
    apply (hasCardinalLT_of_finite ((Δ[h.1 + 2] : SSet.{v}) _⦋n⦌) μ hμ.aleph0_le).of_surjective
      (fun s => (⟨f s, Set.mem_range_self s⟩ : Set.range f))
    rintro ⟨_, s, rfl⟩
    exact ⟨s, rfl⟩
  change HasCardinalLT (A.obj (Opposite.op ⦋n⦌) ∪
    (⨆ h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.InnerHornData A.toSSet, SSet.Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.innerHornFiller A h)).obj
      (Opposite.op ⦋n⦌) : Set (X _⦋n⦌)) μ
  exact hasCardinalLT_union hμ.aleph0_le (hA n)
    (hasCardinalLT_iSup_obj hμ hI _ _ hF)

/-- 概要：一段の内ホーン充填は非退化単体数を μ 未満に保つ。
方針：元の非退化単体の評価を次数へ移し、同じ一段の評価から戻す。
規約：μ は正則非可算。使われ方：元の可算段階の非退化単体数の帰納。 -/
lemma hasCardinalLT_innerHornStep {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    (hω : Cardinal.aleph0 < μ) {X : SSet.{v}} [Quasicategory X] (A : X.Subcomplex)
    (hA : HasCardinalLT A.toSSet.N μ) : HasCardinalLT (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.innerHornStep A).toSSet.N μ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_N_of_obj hμ hω _ (hasCardinalLT_innerHornStep_obj hμ hω A
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_obj_of_N hμ A.toSSet hA))

/-- 概要：各充填段階の非退化単体数は元と同じ μ 未満。
方針：既存の innerHornStage の自然数帰納で一段の評価を適用する。
規約：新しい段階列は作らない。使われ方：可算閉包の入力。 -/
lemma hasCardinalLT_innerHornStage {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    (hω : Cardinal.aleph0 < μ) {X : SSet.{v}} [Quasicategory X] (A : X.Subcomplex)
    (hA : HasCardinalLT A.toSSet.N μ) (k : ℕ) :
    HasCardinalLT (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.innerHornStage A k).toSSet.N μ := by
  induction k with
  | zero => exact hA
  | succ k ih => exact hasCardinalLT_innerHornStep hμ hω _ ih

/-- 概要：元の内ホーン充填閉包の非退化単体数は μ 未満。
方針：同じ可算段階の次数別の和を評価して非退化単体全体へ戻す。
規約：宇宙的 Small の既存証明は変更しない。使われ方：P の μ-small 閉包への接続。 -/
theorem hasCardinalLT_innerHornClosure {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    (hω : Cardinal.aleph0 < μ) {X : SSet.{v}} [Quasicategory X] (A : X.Subcomplex)
    (hA : HasCardinalLT A.toSSet.N μ) : HasCardinalLT (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.innerHornClosure A).toSSet.N μ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_N_of_obj hμ hω
  intro n
  exact hasCardinalLT_iSup_obj hμ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_nat hω) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.innerHornStage A) _
    (fun k => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_obj_of_N hμ _ (hasCardinalLT_innerHornStage hμ hω A hA k) n)

/-- 概要：同じ宇宙の非退化単体濃度の不等式として閉包評価を公開する。
方針：宇宙多相な評価をそのまま簡約する。
規約：F2 の IsKappaSmall は import しない。使われ方：定義展開だけで P の述語へ適用する。 -/
theorem cardinal_innerHornClosure_lt {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    (hω : Cardinal.aleph0 < μ) {X : SSet.{u}} [Quasicategory X] (A : X.Subcomplex)
    (hA : Cardinal.mk A.toSSet.N < μ) : Cardinal.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.innerHornClosure A).toSSet.N < μ := by
  rw [← hasCardinalLT_iff_cardinal_mk_lt] at hA ⊢
  exact hasCardinalLT_innerHornClosure hμ hω A hA

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
