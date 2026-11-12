module
public import SerrePositivity.KST.SConstruction.TerminalPathContractibility
public import SerrePositivity.KST.SConstruction.ZeroRowTerminalFiberHomotopy
public import SerrePositivity.KST.SConstruction.ReductionEquivalence
public import SerrePositivity.KST.Comparison.AlternativeFiberCriterion

/-! # 元の零行と終点固定 fiber の局所化同型
概要：元の零行から終点固定 fiber への二つの実際の比較は正の反復で局所化同型になる。
方針：path 空間の可縮性と元の homotopy pullback を使い、実ホモトピーで零時刻へ移す。
規約：元の loop からの包含との同定は別工程。使われ方：実際の構造射の Ω 条件の検出。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel SerrePositivity.KST.Comparison
open SSet.modelCategoryQuillen
open scoped Simplicial

/-- 終点固定 path 空間の基点包含は全境界充填から局所化同型。 -/
lemma terminalPathBasepoint_localized_isIso (B : PointedSimplicialSet.{u})
    [KanComplex B.right] :
    IsIso (AnodyneHomotopy.anodyneQ.map (terminalPathSpace B).hom) := by
  let Q := AnodyneHomotopy.anodyneQ
  let P := terminalPathSpace B
  have := trivialKanFibration_toUnit_of_contractible (terminalPathSpace_isContractibleKan B)
  have := map_isIso_of_trivialKanFibration Q (Localization.inverts Q anodyneExtensions)
    (toUnit P.right)
  have hi : P.hom ≫ toUnit P.right = 𝟙 _ := isTerminalTensorUnit.hom_ext _ _
  have : IsIso (Q.map P.hom ≫ Q.map (toUnit P.right)) := by
    rw [← Q.map_comp, hi, Q.map_id]
    infer_instance
  exact IsIso.of_isIso_comp_right (Q.map P.hom) (Q.map (toUnit P.right))

/-- 元の零合成の正方形が homotopy pullback なら終点固定 fiber への比較は局所化同型。 -/
lemma terminalStrictZeroFiberMap_localized_isIso_of_homotopyPullback
    {A : SSet.{u}} {E B : PointedSimplicialSet.{u}} [KanComplex B.right]
    (f : E ⟶ B) (a : A ⟶ E.right) (ha : a ≫ f.right = toUnit A ≫ B.hom)
    (h : IsHomotopyPullback (CommSq.mk ha)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (terminalStrictZeroFiberMap f a ha)) := by
  have hp := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (terminalPathStart B) f).lift_fst
    (toUnit A ≫ (terminalPathSpace B).hom) a (by
      rw [Category.assoc, Under.w]
      exact ha.symm)
  have he := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (terminalPathStart B) f).lift_snd
    (toUnit A ≫ (terminalPathSpace B).hom) a (by
      rw [Category.assoc, Under.w]
      exact ha.symm)
  exact (isHomotopyPullback_iff_alternative_fiber (CommSq.mk ha).flip
    (terminalPathSpace B).hom (terminalPathBasepoint_localized_isIso B)
    (terminalPathStart B).right
    ((SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance)
    (Under.w (terminalPathStart B))
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (terminalPathStart B) f).flip
    (terminalStrictZeroFiberMap f a ha) he hp).mp
      ((isHomotopyPullback_flip_iff (CommSq.mk ha)).mpr h)

/-- 元の零行から終点固定 fiber への定数 path による比較は正の反復で局所化同型。 -/
lemma zeroRowTerminalFiberComparison_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (zeroRowTerminalFiberComparison (r + 1) X)) :=
  terminalStrictZeroFiberMap_localized_isIso_of_homotopyPullback
    (pointedFullIteratedPathKanBoundary (r + 1) X) (zeroRowPathToKan (r + 1) X)
    (zeroRowPathToKan_boundary (r + 1) X) (zeroRowKanBoundary_homotopyPullback r X)

/-- 元の零行収縮の境界 loop と全空間の基点の組も同じ fiber への局所化同型。 -/
lemma zeroRowTerminalLoopFiberComparison_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (zeroRowTerminalLoopFiberComparison (r + 1) X)) := by
  rw [AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions)
    (zeroRowTerminalFiberHomotopy (r + 1) X)]
  exact zeroRowTerminalFiberComparison_localized_isIso r X

end SerrePositivity.KST.SConstruction
