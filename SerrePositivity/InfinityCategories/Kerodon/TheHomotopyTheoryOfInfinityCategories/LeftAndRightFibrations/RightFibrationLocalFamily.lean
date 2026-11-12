module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.F1BFibrationsRightAnodyneTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationContractible

/-!
概要：右ファイブレーションの相対 Hom の族を、頂点ごとの可縮性から同時に延長する。
方針：指定した底の族への引き戻しを取り、右ファイブレーションの fiber 判定を使う。
規約：底 K と全パラメータは任意。部分族・始点側・底を厳密に保持する。
使われ方：HTT 5.5.4.5(2)、局所辺の coherent な族の持ち上げの一般的な段階。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

variable {D A E B K : SSet.{u}} (i : D ⟶ A) [Mono i] (p : E ⟶ B)
  [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] (sq : internalHom.PullbackObjObj i p)
  (f : K ⟶ (ihom A).obj B)

/-- 相対内部 Hom の底の図式だけを指定した族へ制限する。 -/
def relativeHomFamilyProjection :
    pullback sq.π (pullback.fst sq.snd f) ⟶ pullback sq.snd f :=
  pullback.snd sq.π (pullback.fst sq.snd f)

/-- 各頂点の完全な持ち上げ空間の可縮性は、族全体の全境界充填性を与える。 -/
lemma relativeHomFamilyProjection_trivial
    (h : ∀ (k : K _⦋0⦌) (b : sq.pt _⦋0⦌),
      sq.snd.app (Opposite.op ⦋0⦌) b = f.app (Opposite.op ⦋0⦌) k →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber sq.π b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (relativeHomFamilyProjection i p sq f) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalRightFibration_pullbackObjObjπ i p sq
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.snd sq.π (pullback.fst sq.snd f))
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_trivialKanFibration_of_contractible_fibers
  intro b
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_pullback_isContractibleKan
  apply h ((pullback.snd sq.snd f).app (Opposite.op ⦋0⦌) b)
  have he := congrArg (fun t ↦ t.app (Opposite.op ⦋0⦌) b)
    (pullback.condition (f := sq.snd) (g := f))
  exact he

/-- 頂点ごとの可縮性から、任意の単射に沿う元の相対 Hom 族を同時に延長する。 -/
lemma relativeHomFamily_exists_extension
    (h : ∀ (k : K _⦋0⦌) (b : sq.pt _⦋0⦌),
      sq.snd.app (Opposite.op ⦋0⦌) b = f.app (Opposite.op ⦋0⦌) k →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber sq.π b))
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (a : T ⟶ sq.pt) (k : T ⟶ K)
    (ha : a ≫ sq.snd = k ≫ f) (l : S ⟶ (ihom A).obj E)
    (hl : l ≫ sq.π = j ≫ a) :
    ∃ L : T ⟶ (ihom A).obj E, j ≫ L = l ∧ L ≫ sq.π = a := by
  have := relativeHomFamilyProjection_trivial i p sq f h
  let v := pullback.lift a k ha
  have hv : v ≫ pullback.fst sq.snd f = a := pullback.lift_fst _ _ _
  let u := pullback.lift l (j ≫ v) (by rw [Category.assoc, hv, hl])
  have hu : u ≫ relativeHomFamilyProjection i p sq f = j ≫ v :=
    pullback.lift_snd _ _ _
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := relativeHomFamilyProjection i p sq f) j
    inferInstance
  have s : CommSq u j (relativeHomFamilyProjection i p sq f) v := ⟨hu⟩
  refine ⟨s.lift ≫ pullback.fst sq.π (pullback.fst sq.snd f), ?_, ?_⟩
  · rw [← Category.assoc, s.fac_left, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (s.lift ≫ relativeHomFamilyProjection i p sq f) ≫ _ = a
    rw [s.fac_right, hv]

/-- 始点側の族と底の族を同時に固定し、指定した部分族を厳密に延長する。 -/
lemma relativeHomFamily_exists_extension_over_base
    (h : ∀ (k : K _⦋0⦌) (b : sq.pt _⦋0⦌),
      sq.snd.app (Opposite.op ⦋0⦌) b = f.app (Opposite.op ⦋0⦌) k →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber sq.π b))
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (d : T ⟶ (ihom D).obj E) (k : T ⟶ K)
    (hd : d ≫ (ihom D).map p = (k ≫ f) ≫ (pre i).app B)
    (l : S ⟶ (ihom A).obj E) (hl : l ≫ (pre i).app E = j ≫ d)
    (hb : l ≫ (ihom A).map p = j ≫ k ≫ f) :
    ∃ L : T ⟶ (ihom A).obj E,
      j ≫ L = l ∧ L ≫ (pre i).app E = d ∧ L ≫ (ihom A).map p = k ≫ f := by
  let a := sq.isPullback.lift d (k ≫ f) hd
  have ha : a ≫ sq.snd = k ≫ f := sq.isPullback.lift_snd _ _ _
  have hl' : l ≫ sq.π = j ≫ a := by
    apply sq.hom_ext
    · rw [Category.assoc, sq.π_fst, Category.assoc, sq.isPullback.lift_fst]
      exact hl
    · rw [Category.assoc, sq.π_snd, Category.assoc, ha]
      exact hb
  obtain ⟨L, hL, hLa⟩ := relativeHomFamily_exists_extension i p sq f h j a k ha l hl'
  refine ⟨L, hL, ?_, ?_⟩
  · have hf : sq.π ≫ sq.fst = (pre i).app E := sq.π_fst
    rw [← hf, ← Category.assoc, hLa]
    exact sq.isPullback.lift_fst _ _ _
  · have hb' : sq.π ≫ sq.snd = (ihom A).map p := sq.π_snd
    rw [← hb', ← Category.assoc, hLa, ha]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
