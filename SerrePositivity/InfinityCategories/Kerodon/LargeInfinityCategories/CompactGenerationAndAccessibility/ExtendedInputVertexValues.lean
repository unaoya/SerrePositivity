module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ExtendedInputVertexData
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.InputCoconeNaturality

/-!
概要：追加入力付き頂点データの全成分値を元の対象圏へ展開する。
方針：保持した厳密な全値の等式へ uncurry を適用し、安定な制限の全値を使う。
規約：元の頂点と全入力を保つ。
使われ方：元の相対余錐の成分値を指定始点側の余錐と合わせる。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

variable (μ : Cardinal.{u}) {K B : SSet.{u + 1}} [Quasicategory B]
  {C L : Fin 2 → SSet.{u + 1}} [∀ c, Quasicategory (C c)]
  (p : ∀ c, C c ⟶ B) (a : K ⟶ pullback (p 0) (p 1)) (z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone a)
  (q : ∀ c, L c ⟶ C c) (i : ∀ c, K ⟶ L c)
  (hi : ∀ c, i c ≫ q c = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullbackComponentInput p a c)
  (zc : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (q c))
  (hzi : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (i c) (𝟙 Δ[0]) ≫ (zc c).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullbackComponentInputCocone p a z c).val)

/-- 概要：元の頂点データの第一全成分は追加入力側の第一全値の制限。
方針：保持された全値の等式を元の対象圏まで展開する。
規約：元の全二点余錐を厳密に保持する。
使われ方：指定第一成分始点の下の全余錐との一致。 -/
lemma ExtendedInputPullbackVertexData.first_uncurry
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ExtendedInputPullbackVertexData μ p a z q i hi zc hzi) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry R.vertex.val ≫ pullback.fst (p 0) (p 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (i 0) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] Δ[0])) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry R.first.val := by
  have hh := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry R.first_value
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputRestriction_val] at hh
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableCosliceRestriction_uncurry] at hh
  exact hh

/-- 概要：元の頂点データの第二全成分は追加入力側の第二全値の制限。
方針：保持された全値の等式を元の対象圏まで展開する。
規約：元の全二点余錐を厳密に保持する。
使われ方：指定第二成分始点の下の全余錐との一致。 -/
lemma ExtendedInputPullbackVertexData.second_uncurry
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ExtendedInputPullbackVertexData μ p a z q i hi zc hzi) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry R.vertex.val ≫ pullback.snd (p 0) (p 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (i 1) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] Δ[0])) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry R.second.val := by
  have hh := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry R.second_value
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableInputRestriction_val] at hh
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.stableCosliceRestriction_uncurry] at hh
  exact hh

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
