module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallTwistedArrowShapes
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallLimitFamilyPreservation
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.LeftFibration

/-!
概要：κ-small な形状の twisted arrow 極限について、同じ κ の filtered 保存を供給する。
方針：P の形状評価と全極限錐族の保存定理を、元の κ のまま接続する。
規約：κ を拡大せず、end の全自然な極限表示そのものは別工程で構成する。
使われ方：P-12 の Hom end 表示の各脚の保存から頂点の保存への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：小さい twisted arrow 形状の空間値極限関手は指定 κ の filtered 余極限を保つ。
方針：P の twisted arrow の κ-small 性を既存の小極限関手へ渡す。
規約：元の κ と元の twisted arrow を使い、存在入力を追加しない。
使われ方：P-12 の end 関手と filtered 余極限の交換。 -/
lemma exists_kappaContinuousTwistedArrowLimitFunctor
    {κ : Cardinal.{u}} [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (K : SSet.{u}) [Quasicategory K] (hK : IsKappaSmall κ K) :
    ∃ R : (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (TwistedArrow K))).obj
        SpaceInfinity.{u} ⟶ SpaceInfinity.{u},
      Nonempty (QCatAdjunction
        (constantFunctorMap ((SSet.uliftFunctor.{u + 1, u}).obj (TwistedArrow K))
          SpaceInfinity.{u}) R) ∧ IsKappaAccessibleFunctor κ R :=
  exists_kappaContinuousSpaceLimitFunctor hκ (TwistedArrow K) (isKappaSmall_twistedArrow hκ hK)

/-- 概要：twisted arrow 上の全極限錐族の各脚の κ-filtered 保存は頂点の保存を与える。
方針：twisted arrow の小ささを宇宙変更し、既存の全自然な極限錐族の定理を使う。
規約：各頂点の同型だけではなく一つの全錐族を入力とする。
使われ方：Fun の Hom の end 表示を構成した後の P-12 の保存判定。 -/
lemma preservesKappaFilteredColimits_twistedArrowLimitFamily_apex
    {κ : Cardinal.{u}} [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (K : SSet.{u}) [Quasicategory K] (hK : IsKappaSmall κ K)
    {C : SSet.{max u v}} [Quasicategory C]
    (F : (SSet.uliftFunctor.{max u v + 1, max u v}).obj C ⟶
      (ihom (join (Δ[0] : SSet.{max u v + 1})
        ((SSet.uliftFunctor.{max u v + 1, max u v}).obj
          (TwistedArrow ((SSet.uliftFunctor.{v, u}).obj K))))).obj
        SpaceInfinity.{max u v})
    (hF : ∀ x : ((SSet.uliftFunctor.{max u v + 1, max u v}).obj C) _⦋0⦌,
      IsLimitCone (functorVertexCone (F.app (Opposite.op ⦋0⦌) x)))
    (hleg : ∀ k : ((SSet.uliftFunctor.{max u v + 1, max u v}).obj
        (TwistedArrow ((SSet.uliftFunctor.{v, u}).obj K))) _⦋0⦌,
      Compact.PreservesKappaFilteredColimits.{u, v} κ (F ≫ evaluateFunctorAt
        ((joinInr (Δ[0] : SSet.{max u v + 1}) _).app (Opposite.op ⦋0⦌) k))) :
    Compact.PreservesKappaFilteredColimits.{u, v} κ (F ≫ evaluateFunctorAt
      (yonedaEquiv (joinInl (Δ[0] : SSet.{max u v + 1}) _))) := by
  have hsmallK : IsKappaSmall (Cardinal.lift.{v} κ)
      ((SSet.uliftFunctor.{v, u}).obj K) := (isKappaSmall_ulift_iff κ K).mpr hK
  have : Fact (Cardinal.lift.{v} κ).IsRegular := ⟨(Fact.out : κ.IsRegular).lift⟩
  have hκ' : Cardinal.aleph0 < Cardinal.lift.{v} κ := by
    have h : Cardinal.lift.{v} Cardinal.aleph0 < Cardinal.lift.{v} κ := Cardinal.lift_lt.mpr hκ
    simpa only [Cardinal.lift_aleph0] using h
  have hsmall : IsKappaSmall (Cardinal.lift.{v} κ)
      (TwistedArrow ((SSet.uliftFunctor.{v, u}).obj K)) :=
    isKappaSmall_twistedArrow hκ' hsmallK
  exact preservesKappaFilteredColimits_limitFamily_apex_of_small hκ hsmall F hF hleg

end SerrePositivity.InfinityCategories.F2.Presentable
