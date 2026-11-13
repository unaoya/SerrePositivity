module
public import SerrePositivity.KST.SConstruction.FiberFromZeroCospans
public import SerrePositivity.KST.SConstruction.FunctorCofibers
public import SerrePositivity.KST.SConstruction.FunctorZeroEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseColimitExistence
public import SerrePositivity.KST.SConstruction.ZeroSpanChoices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitExistence

/-! # 安定な標的の関手圏の安定性
概要：任意の単体集合を始域とする関手 quasicategory は標的が安定なら安定。
方針：零脚を持つ図式の点ごとの極限・余極限と A6 の判定を使う。
規約：有限極限一般の存在は追加仮定しない。使われ方：反復 S• の各段。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：零始点の辺の評価は零始点の辺。
方針：関手頂点の評価式と零対象の評価を使う。
規約：標的は零対象を持つ quasicategory。使われ方：点ごとの零 cospan。 -/
lemma zeroSourceArrow_evaluate {A C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    (e : (Δ[1] : SSet.{u}) ⟶ (ihom A).obj C)
    (he : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex e)) (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a)) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app
    (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a)))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  apply isZeroVertex_evaluateFunctorAt
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app
    (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex e)) at he
  rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at he

/-- 概要：零終点の辺の評価は零終点の辺。
方針：関手頂点の評価式と零対象の評価を使う。
規約：標的は零対象を持つ quasicategory。使われ方：点ごとの零 span。 -/
lemma zeroTargetArrow_evaluate {A C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    (e : (Δ[1] : SSet.{u}) ⟶ (ihom A).obj C)
    (he : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex e)) (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a)) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
    (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a)))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  apply isZeroVertex_evaluateFunctorAt
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
    (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex e)) at he
  rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at he

/-- 概要：関手圏の零脚 cospan の各評価には極限が存在する。
方針：零始点を評価して安定な標的の fiber の存在へ還元する。
規約：A は任意。使われ方：関手圏の fiber の存在と普遍性の反映。 -/
lemma functor_zeroCospan_hasPointwiseLimits {A C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (p : (horn 2 2 : SSet.{u}) ⟶ (ihom A).obj C)
    (hp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₂.ι₁₂ ≫ p))) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasPointwiseLimits p := by
  intro a
  apply hasLimit_zeroCospan (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a)
  exact zeroSourceArrow_evaluate (horn₂₂.ι₁₂ ≫ p) hp a

/-- 概要：関手圏の零脚 span の各評価には余極限が存在する。
方針：零終点を評価して安定な標的の cofiber の存在へ還元する。
規約：A は任意。使われ方：関手圏の押し出し性の反映。 -/
lemma functor_zeroSpan_hasPointwiseColimits {A C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (p : (horn 2 0 : SSet.{u}) ⟶ (ihom A).obj C)
    (hp : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₂ ≫ p))) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasPointwiseColimits p := by
  intro a
  apply hasColimit_zeroSpan (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a)
  exact zeroTargetArrow_evaluate (horn₂₀.ι₀₂ ≫ p) hp a

/-- 概要：関手圏の各辺は fiber 正方形を持つ。
方針：零脚 cospan の点ごとの極限を A6 で関手圏へ移す。
規約：標的だけに安定性を仮定する。使われ方：関手圏の安定性。 -/
lemma functor_fiberSquare_nonempty {A C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    {x y : ((ihom A).obj C) _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj C)) x y) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare f) := by
  apply fiberSquare_nonempty_of_zeroCospan_limits
  intro p hp
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasLimit_of_hasPointwiseLimits p (functor_zeroCospan_hasPointwiseLimits p hp)

/-- 概要：関手圏の零角の引き戻し性は点ごとの引き戻し性と同値。
方針：零脚 cospan の極限の存在を明示して A6 の双方向判定を使う。
規約：任意の四角形への主張に拡張しない。使われ方：fiber と cofiber の一致。 -/
lemma functor_zeroTriangle_pullback_iff {A C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle ((ihom A).obj C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare t.square ↔ ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (t.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) := by
  have hp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₂.ι₁₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square)) := by
    unfold _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((horn₂₂.ι₁₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ t.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge]
    exact t.zero_corner
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_pointwise_of_hasPointwiseLimits
    (functor_zeroCospan_hasPointwiseLimits _ hp) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square)

/-- 概要：関手圏の零角の押し出し性は点ごとの押し出し性と同値。
方針：零脚 span の余極限の存在を明示して点ごとの双方向判定を使う。
規約：任意の四角形への主張に拡張しない。使われ方：fiber と cofiber の一致。 -/
lemma functor_zeroTriangle_pushout_iff {A C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle ((ihom A).obj C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare t.square ↔ ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (t.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) := by
  have hp : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan t.square)) := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroTargetArrow
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ t.square).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
    exact t.zero_corner
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPushoutSquare_iff_pointwise_of_hasPointwiseColimits t.square
    (functor_zeroSpan_hasPointwiseColimits _ hp)

/-- 概要：安定な標的を持つ任意の関手 quasicategory は安定。
方針：零対象と fiber/cofiber を構成し、零角の普遍性を点ごとに判定する。
規約：追加の極限存在仮定を置かない。使われ方：S_n の安定性の反映。 -/
instance functor_isStable (A C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((ihom A).obj C) where
  toHasZeroVertex := functor_hasZeroVertex A C
  fiber_exists f := functor_fiberSquare_nonempty f
  cofiber_exists f := functor_cofiberSquare_nonempty f
  fiber_iff_cofiber t := by
    apply (functor_zeroTriangle_pullback_iff t).trans
    apply Iff.trans _ (functor_zeroTriangle_pushout_iff t).symm
    apply forall_congr'
    intro a
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.fiber_iff_cofiber (⟨t.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a,
      isZeroVertex_evaluateFunctorAt t.zero_corner a⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle C)

end SerrePositivity.KST.SConstruction
