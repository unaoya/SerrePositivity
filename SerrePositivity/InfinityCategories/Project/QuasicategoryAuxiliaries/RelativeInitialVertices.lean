module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundary

/-! # 相対始対象の全部分圏と境界充填

概要：相対始対象全体から基底への射は正次元の全境界を持ち上げる。
方針：境界の最初の頂点の相対始対象性で充填し、全頂点が境界内にあることを使って制限する。
規約：零次元の持ち上げは別に存在を仮定する。
使われ方：S3 の普遍余錐の族の選択。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：相対始点境界充填を持つ頂点が張る全部分単体集合。
方針：各頂点に InitialBoundaryLifting を課す。
規約：ファイブレーション性・存在は定義に含めない。
使われ方：普遍余錐の全部分圏。 -/
def relativeInitialVertices {E B : SSet.{u}} (p : E ⟶ B) : E.Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices E (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p)

/-- 概要：相対始対象全体から基底への射。
方針：全部分複体の包含と元の射を合成する。
規約：元の射に追加条件を課さない。
使われ方：普遍余錐の図式への制限。 -/
def relativeInitialProjection {E B : SSet.{u}} (p : E ⟶ B) :
    (relativeInitialVertices p : SSet.{u}) ⟶ B :=
  (relativeInitialVertices p).ι ≫ p

/-- 概要：相対始対象全体から基底への射は正次元の境界を持ち上げる。
方針：最初の頂点で相対充填し、他の全頂点も境界にあることから全部分圏へ戻す。
規約：quasicategory 性やファイブレーション性は不要。
使われ方：普遍余錐の coherent な選択の一意性。 -/
lemma relativeInitialProjection_hasLiftingProperty_boundary {E B : SSet.{u}}
    (p : E ⟶ B) (n : ℕ) :
    HasLiftingProperty (boundary (n + 1)).ι (relativeInitialProjection p) := by
  constructor
  intro a b sq
  let a' := a ≫ (relativeInitialVertices p).ι
  let x := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ a)
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p x.val := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x
  have hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ a' = SSet.yonedaEquiv.symm x.val := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    rfl
  have hs : CommSq a' (boundary (n + 1)).ι p b := ⟨sq.w⟩
  obtain ⟨F, hF, hFp⟩ := hx n a' b hfirst hs
  have hv : ∀ v : (Δ[n + 1] : SSet.{u}) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p (F.app (Opposite.op ⦋0⦌) v) := by
    intro v
    let w : (boundary (n + 1) : SSet.{u}) _⦋0⦌ :=
      ⟨v, by
        have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v)
        rw [Equiv.symm_apply_apply] at h
        exact h⟩
    have hw := ConcreteCategory.congr_hom (NatTrans.congr_app hF (Opposite.op ⦋0⦌)) w
    change F.app (Opposite.op ⦋0⦌) v = (a.app (Opposite.op ⦋0⦌) w).val at hw
    rw [hw]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) w)
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p) F hv
  have hg : g ≫ (relativeInitialVertices p).ι = F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
  · apply (cancel_mono (relativeInitialVertices p).ι).1
    rw [Category.assoc, hg]
    exact hF
  · change g ≫ (relativeInitialVertices p).ι ≫ p = b
    rw [← Category.assoc, hg, hFp]

/-- 概要：各基底頂点の上に相対始対象があれば射は trivial Kan fibration。
方針：零次元は全射性、正次元は相対始対象の境界充填を使う。
規約：存在条件は頂点上の全射性として明記する。
使われ方：図式の族に沿う普遍余錐の選択とその一意性。 -/
lemma relativeInitialProjection_trivialKanFibration {E B : SSet.{u}} (p : E ⟶ B)
    (hsurj : Function.Surjective ((relativeInitialProjection p).app (Opposite.op ⦋0⦌))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (relativeInitialProjection p) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  cases n with
  | zero =>
    constructor
    intro a b sq
    obtain ⟨x, hx⟩ := hsurj (SSet.yonedaEquiv b)
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm x
      fac_left := boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, hx]
  | succ n => exact relativeInitialProjection_hasLiftingProperty_boundary p n

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
