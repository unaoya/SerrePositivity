module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.LiftedIntervalCospanEquivalence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.UniverseKanPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.StrictKanPullbackMapEquivalence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalPullbackCoordinates

/-!
概要：小さい interval 引き戻しの持ち上げから、大きい厳密な引き戻しへの実比較。
方針：元の全 path から厳密化した左成分と、元の右成分を同じ引き戻しへ入れる。
規約：元の二射影の式を保持。使われ方：実 fiber 模型から native 切断模型への同値。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.F2
variable {X Y Z : SSet.{u}} [KanComplex X] [KanComplex Y] [KanComplex Z]
  {L M R : SSet.{max u v}} [KanComplex L] [KanComplex M] [KanComplex R]
  (f : X ⟶ Z) (g : Y ⟶ Z) (p : L ⟶ M) (q : R ⟶ M) [Fibration p]
  (s : (SSet.uliftFunctor.{v, u}).obj X ⟶ L)
  (r : (SSet.uliftFunctor.{v, u}).obj Y ⟶ R)
  (t : (SSet.uliftFunctor.{v, u}).obj Z ⟶ M)
  (hs : (SSet.uliftFunctor.{v, u}).map f ≫ t = s ≫ p)
  (hr : (SSet.uliftFunctor.{v, u}).map g ≫ t = r ≫ q)

include hs hr in
/-- 元の interval 置換の宇宙持ち上げから、同じ三成分による厳密な cospan 比較。 -/
def liftedIntervalCospanComparison :
    cospan ((SSet.uliftFunctor.{v, u}).map (intervalReplacementEndpoint f))
      ((SSet.uliftFunctor.{v, u}).map g) ⟶ cospan p q := by
  let a : (SSet.uliftFunctor.{v, u}).obj (intervalReplacement f) ⟶ L :=
    liftedIntervalCospanLeft f p s t hs
  exact cospanHomMk t a r (liftedIntervalCospanLeft_over f p s t hs).symm hr

include hs hr in
/-- 元の小さい二段の引き戻しを持ち上げて、切断側の厳密な引き戻しへ写す比較。 -/
def liftedIntervalPullbackComparison :
    (SSet.uliftFunctor.{v, u}).obj (intervalPullback f g) ⟶ pullback p q :=
  (uliftPullbackIso.{u, v} (intervalReplacementEndpoint f) g).hom ≫
    pullback.map _ _ p q (liftedIntervalCospanLeft f p s t hs) r t
      (liftedIntervalCospanLeft_over f p s t hs).symm hr

/-- 第一射影は元の第一段の射影に、同じ指定 path で厳密化した左成分を合成したもの。 -/
lemma liftedIntervalPullbackComparison_left :
    liftedIntervalPullbackComparison f g p q s r t hs hr ≫ pullback.fst p q =
      (SSet.uliftFunctor.{v, u}).map (pullback.fst (intervalReplacementEndpoint f) g) ≫
        liftedIntervalCospanLeft f p s t hs := by
  rw [liftedIntervalPullbackComparison, Category.assoc, pullback.map, pullback.lift_fst,
    ← Category.assoc, uliftPullbackIso_fst]

/-- 第二射影は元の同じ右入力の射影を持ち上げたもの。 -/
lemma liftedIntervalPullbackComparison_right :
    liftedIntervalPullbackComparison f g p q s r t hs hr ≫ pullback.snd p q =
      (SSet.uliftFunctor.{v, u}).map (intervalPullbackRight f g) ≫ r := by
  rw [liftedIntervalPullbackComparison, Category.assoc, pullback.map, pullback.lift_snd,
    ← Category.assoc, uliftPullbackIso_snd]
  rfl

/-- 元の三成分が同値なら、同じ全 path を用いた引き戻し比較はホモトピー同値。 -/
lemma liftedIntervalPullbackComparison_homotopyEquivalence
    (es : IsSimplicialHomotopyEquivalence s) (er : IsSimplicialHomotopyEquivalence r)
    (et : IsSimplicialHomotopyEquivalence t) :
    IsSimplicialHomotopyEquivalence (liftedIntervalPullbackComparison f g p q s r t hs hr) := by
  have := uliftMap_fibration.{u, v} (intervalReplacementEndpoint f)
  have : KanComplex (pullback (intervalReplacementEndpoint f) g) :=
    inferInstanceAs (KanComplex (intervalPullback f g))
  have : KanComplex (pullback ((SSet.uliftFunctor.{v, u}).map (intervalReplacementEndpoint f))
      ((SSet.uliftFunctor.{v, u}).map g)) :=
    HomotopyLimits.pullback_kanComplex_of_fibration _ _
  have : KanComplex (pullback p q) := HomotopyLimits.pullback_kanComplex_of_fibration p q
  exact (HomotopyLimits.homotopyEquivalence_of_isIso
    (uliftPullbackIso.{u, v} (intervalReplacementEndpoint f) g).hom).comp
      (strictKanPullbackMap_homotopyEquivalence _ _ p q _ r t _ hr
        (liftedIntervalCospanLeft_homotopyEquivalence f p s t hs es) er et)

end SerrePositivity.InfinityCategories.F2
