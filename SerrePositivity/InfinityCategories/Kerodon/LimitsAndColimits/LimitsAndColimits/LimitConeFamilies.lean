module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitCriterion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-! # 相対終対象の全部分圏と境界充填

概要：相対終対象全体から基底への射は正次元の全境界を持ち上げる。
方針：境界の最後の頂点の相対終対象性で充填し、全頂点が境界内にあることを使って制限する。
規約：零次元の持ち上げは別に存在を仮定する。
使われ方：S3 の普遍錐の族の選択。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：相対終点境界充填を持つ頂点が張る全部分単体集合。
方針：各頂点に TerminalBoundaryLifting を課す。
規約：ファイブレーション性・存在は定義に含めない。
使われ方：普遍錐の全部分圏。 -/
def relativeTerminalVertices {E B : SSet.{u}} (p : E ⟶ B) : E.Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices E (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p)

/-- 概要：相対終対象全体から基底への射。
方針：全部分複体の包含と元の射を合成する。
規約：元の射に追加条件を課さない。
使われ方：普遍錐の図式への制限。 -/
def relativeTerminalProjection {E B : SSet.{u}} (p : E ⟶ B) :
    (relativeTerminalVertices p : SSet.{u}) ⟶ B :=
  (relativeTerminalVertices p).ι ≫ p

/-- 概要：相対終対象全体から基底への射は正次元の境界を持ち上げる。
方針：最後の頂点で相対充填し、他の全頂点も境界にあることから全部分圏へ戻す。
規約：quasicategory 性やファイブレーション性は不要。
使われ方：普遍錐の coherent な選択の一意性。 -/
lemma relativeTerminalProjection_hasLiftingProperty_boundary {E B : SSet.{u}}
    (p : E ⟶ B) (n : ℕ) :
    HasLiftingProperty (boundary (n + 1)).ι (relativeTerminalProjection p) := by
  constructor
  intro a b sq
  let a' := a ≫ (relativeTerminalVertices p).ι
  let x := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ a)
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p x.val := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x
  have hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ a' = SSet.yonedaEquiv.symm x.val := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    rfl
  have hs : CommSq a' (boundary (n + 1)).ι p b := ⟨sq.w⟩
  obtain ⟨F, hF, hFp⟩ := hx n a' b hfirst hs
  have hv : ∀ v : (Δ[n + 1] : SSet.{u}) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p (F.app (Opposite.op ⦋0⦌) v) := by
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
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p) F hv
  have hg : g ≫ (relativeTerminalVertices p).ι = F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  refine CommSq.HasLift.mk' { l := g, fac_left := ?_, fac_right := ?_ }
  · apply (cancel_mono (relativeTerminalVertices p).ι).1
    rw [Category.assoc, hg]
    exact hF
  · change g ≫ (relativeTerminalVertices p).ι ≫ p = b
    rw [← Category.assoc, hg, hFp]

/-- 概要：普遍錐全体からなる全部分単体集合。
方針：錐の制限射の相対終対象を取る。
規約：quasicategory を値域とすると通常の極限性に一致する。
使われ方：S3 の loop 図式の境界延長。 -/
def limitCones (K X : SSet.{u}) : SSet.{u} :=
  (relativeTerminalVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) : SSet.{u})

/-- 概要：普遍錐の図式への制限射。
方針：相対終対象の全部分圏から基底への射影を使う。
規約：任意の形状の錐の族を扱う。
使われ方：S3 の cospan の族の上での普遍錐の充填。 -/
def limitConeProjection (K X : SSet.{u}) : limitCones K X ⟶ (ihom K).obj X :=
  relativeTerminalProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
