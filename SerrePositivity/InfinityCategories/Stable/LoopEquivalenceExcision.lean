module
public import SerrePositivity.InfinityCategories.Stable.ExcisionRepresentableLimits
public import SerrePositivity.InfinityCategories.Stable.TwoZeroCornerBicartesianOfEquivalence
public import SerrePositivity.InfinityCategories.Stable.FiniteOppositeColimits
public import SerrePositivity.InfinityCategories.Stable.StableOpposite

/-!
概要：有限極限と実 loop 関手の同値性から、任意の引き戻しの押し出し性を得る。
方針：反対圏の有限余極限で切除格子を作り、表現可能前層で判定する。
規約：元の圏の有限余極限や安定性を追加仮定にしない。
使われ方：HA 1.4.2.27 の安定性判定の一般零角への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：元の圏の反対圏では全ての懸垂四角形が引き戻しである。
方針：二つの零角を保つ双対化で既存の loop 判定へ戻す。
規約：元の有限余極限は仮定しない。使われ方：反対圏の切除の四面。 -/
lemma SuspensionSquare.op_isPullback_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    {x : X.op _⦋0⦌} (t : SuspensionSquare x) : IsPullbackSquare t.square := by
  let q := (SSet.opFunctorCompOpFunctorIso.app X).hom
  let F := dualSquare t.square ≫ q
  have hz : IsZeroVertex (squareVertex F 0 1) := t.zero_corner.unop
  have hw : IsZeroVertex (squareVertex F 1 0) := t.other_zero.unop
  have hF : IsPullbackSquare F :=
    (isPullbackSquare_iff_postcomp_isIso _ q).mp
      ((isPushoutSquare_iff_dualSquare t.square).mp t.isPushout)
  have hp := (isPullbackSquare_iff_isPushout_of_zeroCorners_of_loopEquivalence
    s hs hΩ F hz hw).mp hF
  exact (isPullbackSquare_iff_dualSquare t.square).mpr
    ((isPushoutSquare_iff_postcomp_isIso _ q).mpr hp)

/-- 概要：実 loop 同値を持つ pointed な圏では全引き戻しが押し出しである。
方針：反対圏で任意の元の面を保つ格子を作り、その四つの懸垂面を使う。
規約：有限極限だけを入力し、一般安定性や有限余極限を仮定しない。
使われ方：一般の零角に対する fiber/cofiber 判定の順方向。 -/
theorem isPushoutSquare_of_isPullback_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hR : IsPullbackSquare R) :
    IsPushoutSquare R := by
  let z := chosenZeroVertex X.op
  obtain ⟨d⟩ := excisionSquareGrid_nonempty (dualSquare R) z.vertex z.isTerminal
  have hdual := (isPullbackSquare_iff_dualSquare R).mp hR
  have h := excisionFullInput_isPullback_of_suspension_faces d.extension.full (by
    intro i j
    have ht := d.suspension_at_isSuspension z.isZero hdual i j
    let t : SuspensionSquare
        (squareVertex (excisionGridSuspensionAt i j ≫ d.extension.full) 0 0) := {
      square := excisionGridSuspensionAt i j ≫ d.extension.full
      zero_corner := ht.1
      source_eq := rfl
      other_zero := ht.2.1
      isPushout := ht.2.2 }
    exact t.op_isPullback_of_loopEquivalence s hs hΩ)
  rw [d.square_restriction] at h
  exact (isPushoutSquare_iff_dualSquare R).mpr h

end SerrePositivity.InfinityCategories
