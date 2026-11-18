module

public import SerrePositivity.EInfinity.PowerOperation.MayClosedCycles
public import SerrePositivity.EInfinity.PowerOperation.MayFreeProbeHomotopy

/-!
# 自由 probe のための閉元の指定持ち上げ

May, Proposition 2.3 の代表元独立性の補助。
既存の cofibrant probe の比較は全次数全射な擬同型なので、元の閉元を厳密に持ち上げる。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles
variable (k : Type u) [CommRing k]

lemma mayProbeComparison_surjective (K : Complex k) (i : ℤ) :
    Function.Surjective ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison k K).f i) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory k
  have h := ((carrierProbeFactorization k).factorizationData (initial.to K)).hp.1
  exact h i

/-- 各閉元は、元の probe の閉元の厳密な像である。 -/
lemma mayProbeClosed_surjective (K : Complex k) (i : ℤ) :
    Function.Surjective (mayClosedMap (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison k K) i) := by
  intro a
  let f := _root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison k K
  have hb := complex_boundary_lifting_of_surjective_quasiIso k f
    (mayProbeComparison_surjective k K) (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison_quasiIso k K) i
  obtain ⟨b, hd, hf⟩ := hb 0 a.val (by
    exact ((f.f (i + 1)).hom.map_zero).trans a.property.symm)
  exact ⟨⟨b, hd⟩, Subtype.ext hf⟩

/-- 同じ比較射に関する閉元の指定持ち上げ。自然な選択とは主張しない。 -/
def mayProbeClosedLift (K : Complex k) (i : ℤ) (a : MayClosed K i) :
    MayClosed ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor k).obj K) i :=
  Classical.choose (mayProbeClosed_surjective k K i a)

lemma mayProbeClosedLift_spec (K : Complex k) (i : ℤ) (a : MayClosed K i) :
    mayClosedMap (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison k K) i
      (mayProbeClosedLift k K i a) = a :=
  Classical.choose_spec (mayProbeClosed_surjective k K i a)

end SerrePositivity.EInfinity.PowerOperation
