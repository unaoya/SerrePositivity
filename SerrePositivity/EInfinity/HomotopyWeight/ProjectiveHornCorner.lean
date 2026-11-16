module
public import SerrePositivity.EInfinity.HomotopyWeight.ProjectiveHornGenerators
public import SerrePositivity.EInfinity.HomotopyWeight.ConeLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedCorner

/-!
概要：射影anodyneな重みの射とパラメーター単射の相対テンソルは、点ごとのfibrationを持ち上げる。
方針：同じ相対テンソルをpointwiseな二変数随伴へ渡し、各値の内部Homのfibration性を使う。
規約：IS-W2 R03a.1の証明分割。図式モデル構造は使わない。
使われ方：Kan係数への重み制限の全境界の持ち上げ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet MonoidalCategory HomotopicalAlgebra
open SerrePositivity.PointwiseAdjunction
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial SSet.modelCategoryQuillen
variable (I : Type u) [SmallCategory I]

/-- 同じ重みの射の相対テンソルは、各値のKan fibrationに対して左持ち上げ性。 -/
theorem projectiveHorn_corner_lifting {V W F G : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hj : (horns I).rlp.llp j) {A B : SSet.{u}} (f : A ⟶ B) [Mono f]
    (p : F ⟶ G) (hp : ∀ i, Fibration (p.app i)) :
    HasLiftingProperty (weightedCorner j f).ι p := by
  let adj := PointwiseAdjunction.adjunction I
    (ParametrizedAdjunctionTransport.left MonoidalClosed.internalHomAdjunction₂
      (BraidedCategory.curriedBraidingNatIso SSet.{u}))
  let sq : (pointwise I (curriedTensor SSet.{u}).flip).PushoutObjObj f j :=
    { pt := (weightedCorner j f).pt
      inl := (weightedCorner j f).inr
      inr := (weightedCorner j f).inl
      isPushout := (weightedCorner j f).isPushout.flip
      ι := (weightedCorner j f).ι
      inl_ι := (weightedCorner j f).inr_ι
      inr_ι := (weightedCorner j f).inl_ι }
  let pull := Functor.PullbackObjObj.ofHasPullback
    (pointwise I (MonoidalClosed.internalHom (C := SSet.{u}))) f p
  apply (adj.hasLiftingProperty_iff sq pull).mpr
  apply hj
  rw [horns_rlp]
  intro i
  letI pFibration := hp i
  exact (SSet.modelCategoryQuillen.fibration_iff _).mp
    (SSet.fibration_pullbackObjObjπ
      (evaluatePullbackObjObj I _ f p pull i))

end SerrePositivity.EInfinity.HomotopyWeight
