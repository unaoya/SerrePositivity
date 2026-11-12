module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberBoundaryPrefixEquation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanPrefixReplacementTransport

/-! # 候補データの最初の脚側方程式

概要：左右の候補は M 側・零角側の未知成分を零とした方程式を満たす。
方針：先頭置換後の脚側右辺を射影の式で消し、N 側置換はこの集合に影響しないことを使う。
規約：HA Proposition 1.3.1.10。使われ方：残る未知方程式の直接検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 零角への射影との合成は零残差の負。 -/
lemma dgModuleFiberBoundaryUnknownA_projectionZero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    compose A (0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleZero A D)) 0)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownA A D f b hb)
      (add_zero (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n + 1)) =
      -_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsZero A D f b hb := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsZero_eq_zero, neg_zero]

/-- 概要：最後の末尾頂点は最初の末尾頂点を加えた先頭集合に属さない。
方針：二つの末尾頂点の相違と先頭集合の上界を使う。
規約：HTT §1.2.13。使われ方：N 側置換が M 側・零角側を変えないこと。 -/
lemma cospanLast_notMem_insert_firstTail (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n ∉ insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) := by
  simp only [Finset.mem_insert, not_or]
  exact ⟨ne_of_gt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n),
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanTail_notMem_prefix _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n))⟩

/-- 概要：Left 側基底の先頭成分だけを明示解 a へ置き換える。
方針：固定一射の置換を先頭集合へ適用する。
規約：HA Proposition 1.3.1.10。使われ方：二回の置換のうち脚側に影響する段階を分離する。 -/
def dgModuleFiberBoundaryLeftPrefixCandidate {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) (n + 3) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftBase A D f b).replaceFixed (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n + 1)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]; omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces_max n _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]; dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree]; push_cast; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftNative A D f b hb).1.val

/-- 概要：Left 側の先頭置換後の最初の脚側右辺は零。
方針：右辺の変化を型付き Hom へ移し、先頭解の射影が残差の負であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：脚側の未知成分を零に取る方程式。 -/
lemma dgModuleFiberBoundaryLeftPrefixCandidate_first_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryLeftPrefixCandidate A D f b hb).cospanOneTailRhs
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) = 0 := by
  unfold dgModuleFiberBoundaryLeftPrefixCandidate _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanOneTailRhs_replace_prefix_zero_of_heq (A := A) (D := RightModule A D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftBase A D f b) _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftBase_prefixHom A D f b)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)
    rfl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_apex A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_M A D f b hb)
    rfl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownA A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsM A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D f)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftNative A D f b hb).1.property
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsM_heq_raw A D f b hb).symm
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_projection_heq A D f b hb
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownA_projection]
    exact add_neg_cancel _

/-- 概要：Left 側の二成分を挿入した最終候補の最初の脚側右辺は零。
方針：N 側置換の局所性で先頭置換だけの右辺に戻す。
規約：HA Proposition 1.3.1.10。使われ方：最初の脚側方程式の右辺を消去する。 -/
lemma dgModuleFiberBoundaryLeftCandidate_first_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate A D f b hb).cospanOneTailRhs
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) = 0 := by
  have hnot : ¬ insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) ⊆
      insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) := by
    intro hsub
    exact cospanLast_notMem_insert_firstTail n (hsub (Finset.mem_insert_self _ _))
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanOneTailRhs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_replaceFixed_of_not_subset (hnot := hnot)]
  exact dgModuleFiberBoundaryLeftPrefixCandidate_first_rhs_zero A D f b hb

/-- 概要：Left 側候補は最初の末尾頂点を加えた集合の方程式を満たす。
方針：この未知成分は零であり、計算した右辺も零であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：未知 M 側・零角側成分の方程式を完了する。 -/
lemma dgModuleFiberBoundaryLeftCandidate_first_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate A D f b hb).Equation
      (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) := by
  have h0 : insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n := by
    intro heq
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanTail_notMem_prefix _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)
      (heq ▸ Finset.mem_insert_self _ _)
  have hD : insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) ≠
      insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) := by
    intro heq
    exact cospanLast_notMem_insert_firstTail n (heq.symm ▸ Finset.mem_insert_self _ _)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate A D f b hb)
    (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (-(n : ℤ) - 1)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefix_insert _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)]; omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefix_insert_min _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefix_insert_max _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefix_insert _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)]; push_cast; omega)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate_unknown_zero A D f b hb _ (Finset.subset_insert _ _) h0 hD]
  change _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A 0 =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryLeftCandidate A D f b hb).cospanOneTailRhs
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)
  rw [dgModuleFiberBoundaryLeftCandidate_first_rhs_zero]
  exact map_zero _

/-- 概要：Right 側基底の先頭成分だけを明示解 a へ置き換える。
方針：固定一射の置換を先頭集合へ適用する。
規約：HA Proposition 1.3.1.10。使われ方：二回の置換のうち脚側に影響する段階を分離する。 -/
def dgModuleFiberBoundaryRightPrefixCandidate {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) (n + 3) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightBase A D f b).replaceFixed (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree n + 1)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]; omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces_min n _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces_max n _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefixFaces]; dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryDegree]; push_cast; omega)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightNative A D f b hb).1.val

/-- 概要：Right 側の先頭置換後の最初の脚側右辺は零。
方針：右辺の変化を型付き Hom へ移し、先頭解の射影が残差の負であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：脚側の未知成分を零に取る方程式。 -/
lemma dgModuleFiberBoundaryRightPrefixCandidate_first_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    (dgModuleFiberBoundaryRightPrefixCandidate A D f b hb).cospanOneTailRhs
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) = 0 := by
  unfold dgModuleFiberBoundaryRightPrefixCandidate _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanOneTailRhs_replace_prefix_zero_of_heq (A := A) (D := RightModule A D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightBase A D f b) _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightBase_prefixHom A D f b)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundarySource_right_eq A D f b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_apex A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_zero A D f b hb)
    rfl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryUnknownA A D f b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsZero A D f b hb)
    (0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleZero A D)) 0)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fixedHomFamily_heq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightNative A D f b hb).1.property
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRhsZero_heq_raw A D f b hb).symm
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_projection_heq A D f b hb
  · rw [dgModuleFiberBoundaryUnknownA_projectionZero]
    exact add_neg_cancel _

/-- 概要：Right 側の二成分を挿入した最終候補の最初の脚側右辺は零。
方針：N 側置換の局所性で先頭置換だけの右辺に戻す。
規約：HA Proposition 1.3.1.10。使われ方：最初の脚側方程式の右辺を消去する。 -/
lemma dgModuleFiberBoundaryRightCandidate_first_rhs_zero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate A D f b hb).cospanOneTailRhs
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) = 0 := by
  have hnot : ¬ insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) ⊆
      insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) := by
    intro hsub
    exact cospanLast_notMem_insert_firstTail n (hsub (Finset.mem_insert_self _ _))
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanOneTailRhs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_replaceFixed_of_not_subset (hnot := hnot)]
  exact dgModuleFiberBoundaryRightPrefixCandidate_first_rhs_zero A D f b hb

/-- 概要：Right 側候補は最初の末尾頂点を加えた集合の方程式を満たす。
方針：この未知成分は零であり、計算した右辺も零であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：未知 M 側・零角側成分の方程式を完了する。 -/
lemma dgModuleFiberBoundaryRightCandidate_first_equation {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate A D f b hb).Equation
      (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) := by
  have h0 : insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) ≠ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n := by
    intro heq
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanTail_notMem_prefix _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)
      (heq ▸ Finset.mem_insert_self _ _)
  have hD : insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) ≠
      insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n) := by
    intro heq
    exact cospanLast_notMem_insert_firstTail n (heq.symm ▸ Finset.mem_insert_self _ _)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.equation_of_fixed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate A D f b hb)
    (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n)) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (-(n : ℤ) - 1)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefix_insert _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)]; omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefix_insert_min _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefix_insert_max _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n) _)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_cospanPrefix_insert _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)]; push_cast; omega)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate_unknown_zero A D f b hb _ (Finset.subset_insert _ _) h0
    hD]
  change _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A 0 =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundaryRightCandidate A D f b hb).cospanOneTailRhs
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)
  rw [dgModuleFiberBoundaryRightCandidate_first_rhs_zero]
  exact map_zero _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
