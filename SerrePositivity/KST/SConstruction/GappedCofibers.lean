module
public import SerrePositivity.KST.SConstruction.GappedColimitCocones
public import SerrePositivity.KST.SConstruction.ZeroPreservation

/-! # S_n の包含による cofiber の保存と反映
概要：S_n の零角つき正方形が cofiber であることは、Ar の各点で cofiber であることと同値。
方針：零角から必要な点ごとの余極限の存在を供給し、gapped 補完と一意性で保存を示す。
規約：追加の点ごとの存在仮定を残さない。使われ方：反復 S• の構造射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：S_n の零角つき四角形を Ar 図式圏に含める。
方針：gapped 包含の零対象保存を使う。
規約：C は零対象を持つ quasicategory。使われ方：点ごとの cofiber の存在条件。 -/
def gappedInclusionZeroTriangle {n : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle (sConstruction n C)) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle ((ihom (arNerve n)).obj C) :=
  ⟨t.square ≫ (gappedSubcomplex n C).ι, gappedInclusion_isZeroVertex n t.zero_corner⟩

/-- 概要：S_n の零角つき正方形の包含後の span は点ごとの余極限を持つ。
方針：零角を評価し、安定な C の零脚 span の余極限を使う。
規約：点ごとの存在を追加仮定しない。使われ方：包含の cofiber 保存。 -/
lemma gappedInclusion_zeroSpan_hasPointwiseColimits {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle (sConstruction n C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasPointwiseColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan t.square ≫ (gappedSubcomplex n C).ι) := by
  let T := gappedInclusionZeroTriangle t
  have hp : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan T.square)) := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ T.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
    exact T.zero_corner
  exact functor_zeroSpan_hasPointwiseColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan T.square) hp

/-- 概要：S_n の包含は cofiber 正方形の普遍性を保ち反映する。
方針：零角から点ごとの存在を供給し、包含による普遍余錐の双方向判定を使う。
規約：任意の押し出しへの主張とは区別する。使われ方：構造射の cofiber 保存。 -/
lemma gappedInclusion_cofiber_iff {n : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle (sConstruction n C)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (t.square ≫ (gappedSubcomplex n C).ι) := by
  have h := isColimitCone_gappedInclusion_iff_of_hasPointwiseColimits
    (gappedInclusion_zeroSpan_hasPointwiseColimits t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone t.square)
  apply h.trans
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq _ _ (Category.assoc _ _ _)

/-- 概要：S_n の cofiber 正方形の普遍性は Ar の全点で判定できる。
方針：包含による双方向判定と関手圏の点ごとの判定を合わせる。
規約：標的 C の安定性だけを仮定する。使われ方：面・退化と後合成の保存。 -/
lemma gappedInclusion_cofiber_iff_pointwise {n : ℕ} {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle (sConstruction n C)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t ↔ ∀ a : (arNerve n) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (t.square ≫ (gappedSubcomplex n C).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) :=
  (gappedInclusion_cofiber_iff t).trans
    (functor_zeroTriangle_pushout_iff (gappedInclusionZeroTriangle t))

end SerrePositivity.KST.SConstruction
