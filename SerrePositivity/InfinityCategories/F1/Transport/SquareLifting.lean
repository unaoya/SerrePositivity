module

public import SerrePositivity.InfinityCategories.F1.Transport.SquareRestriction
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftAnodynePushoutProduct

/-!
概要：四角形の空間の制限に対する相対持ち上げ。
方針：分類図式を先に延長し、pointed space 側を相対内部 Hom の持ち上げで延長する。
規約：二つの延長は同じ底の図式を厳密に被覆する。
使われ方：Kerodon Lemma 5.6.8.10、制限写像の持ち上げ性の分解。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：四角形の制限の持ち上げは分類図式と相対内部 Hom の二つの持ち上げから得られる。
方針：分類図式を延長し、その図式を底とする pointed space 値の族を延長する。
規約：持ち上げる射 i は任意で、ホーンへの制限は不要。
使われ方：Kerodon Lemma 5.6.8.10、制限の相対充填の共通部分。 -/
lemma hasLiftingProperty_transportSquareRestriction {E B D T U : SSet.{u + 1}}
    (p : E ⟶ B) (g : D ⟶ B) (i : T ⟶ U)
    (r : internalHom.PullbackObjObj (pullback.fst p g) pointedSpaceProjection)
    [HasLiftingProperty i ((pre g).app SpaceInfinity.{u})] [HasLiftingProperty i r.π] :
    HasLiftingProperty i (transportSquareRestriction p g) := by
  constructor
  intro a b sq
  let P := transportSquarePointed p
  let Q := transportSquareDiagram p
  let P₀ := transportSquarePointed (pullback.snd p g)
  let Q₀ := transportSquareDiagram (pullback.snd p g)
  have hP : a ≫ P ≫ (pre (pullback.fst p g)).app PointedSpaceInfinity = i ≫ b ≫ P₀ := by
    dsimp only [P, P₀]
    rw [← transportSquareRestriction_pointed, ← Category.assoc,
      sq.w, Category.assoc]
  have hQ : a ≫ Q ≫ (pre g).app SpaceInfinity = i ≫ b ≫ Q₀ := by
    dsimp only [Q, Q₀]
    rw [← transportSquareRestriction_diagram, ← Category.assoc,
      sq.w, Category.assoc]
  let sqQ : CommSq (a ≫ Q) i ((pre g).app SpaceInfinity) (b ≫ Q₀) := ⟨by
    simpa only [Category.assoc] using hQ⟩
  let F := sqQ.lift
  have hF₀ : i ≫ F = a ≫ Q := sqQ.fac_left
  have hFg : F ≫ (pre g).app SpaceInfinity = b ≫ Q₀ := sqQ.fac_right
  have hbase : (b ≫ P₀) ≫ (ihom (pullback p g)).map pointedSpaceProjection =
      (F ≫ (pre p).app SpaceInfinity) ≫ (pre (pullback.fst p g)).app SpaceInfinity := by
    rw [Category.assoc, transportSquareSpace_condition]
    rw [Category.assoc, ← NatTrans.comp_app, ← pre_map, pullback.condition,
      pre_map, NatTrans.comp_app, ← Category.assoc F, hFg, Category.assoc]
  let V := r.isPullback.lift (b ≫ P₀) (F ≫ (pre p).app SpaceInfinity) hbase
  have hVfst : V ≫ r.fst = b ≫ P₀ := r.isPullback.lift_fst _ _ _
  have hVsnd : V ≫ r.snd = F ≫ (pre p).app SpaceInfinity := r.isPullback.lift_snd _ _ _
  let sqP : CommSq (a ≫ P) i r.π V := ⟨by
    apply r.hom_ext
    · simp only [Category.assoc, r.π_fst, hVfst]
      exact hP
    · simp only [Category.assoc, r.π_snd, hVsnd]
      change a ≫ P ≫ (ihom E).map pointedSpaceProjection = i ≫ F ≫ (pre p).app SpaceInfinity
      dsimp only [P, Q] at hF₀ ⊢
      rw [transportSquareSpace_condition, ← Category.assoc i, hF₀, Category.assoc]⟩
  let H := sqP.lift
  have hHbase : H ≫ (ihom E).map pointedSpaceProjection = F ≫ (pre p).app SpaceInfinity := by
    calc
      _ = (H ≫ r.π) ≫ r.snd := by rw [Category.assoc, r.π_snd]; rfl
      _ = _ := (congrArg (fun f ↦ f ≫ r.snd) sqP.fac_right).trans hVsnd
  have hHrest : H ≫ (pre (pullback.fst p g)).app PointedSpaceInfinity = b ≫ P₀ := by
    calc
      _ = (H ≫ r.π) ≫ r.fst := by rw [Category.assoc, r.π_fst]; rfl
      _ = _ := (congrArg (fun f ↦ f ≫ r.fst) sqP.fac_right).trans hVfst
  let L : U ⟶ transportSquareSpace p := pullback.lift H F hHbase
  have hLP : L ≫ P = H := pullback.lift_fst _ _ _
  have hLQ : L ≫ Q = F := pullback.lift_snd _ _ _
  refine CommSq.HasLift.mk' { l := L, fac_left := ?_, fac_right := ?_ }
  · apply pullback.hom_ext
    · change i ≫ L ≫ P = a ≫ P
      rw [hLP]
      exact sqP.fac_left
    · change i ≫ L ≫ Q = a ≫ Q
      rw [hLQ]
      exact hF₀
  · apply pullback.hom_ext
    · change L ≫ transportSquareRestriction p g ≫ P₀ = b ≫ P₀
      dsimp only [P₀]
      rw [transportSquareRestriction_pointed, ← Category.assoc]
      change (L ≫ P) ≫ _ = _
      rw [hLP]
      exact hHrest
    · change L ≫ transportSquareRestriction p g ≫ Q₀ = b ≫ Q₀
      dsimp only [Q₀]
      rw [transportSquareRestriction_diagram, ← Category.assoc]
      change (L ≫ Q) ≫ _ = _
      rw [hLQ]
      exact hFg

/-- 概要：単射な底の制限は四角形の空間の inner fibration を与える。
方針：分類図式の制限の inner fibration と相対内部 Hom の left fibration を使う。
規約：p の fibration 性を要求せず、表現条件の部分空間の持ち上げ性は別に検証する。
使われ方：Kerodon Lemma 5.6.8.10、周囲の四角形の制限の内ホーン充填。 -/
instance transportSquareRestriction_innerFibration {E B D : SSet.{u + 1}}
    (p : E ⟶ B) (g : D ⟶ B) [Mono g] : InnerFibration (transportSquareRestriction p g) where
  mem := by
    intro T U i hi
    let r := Functor.PullbackObjObj.ofHasPullback internalHom
      (pullback.fst p g) pointedSpaceProjection
    have : LeftFibration r.π :=
      leftFibration_pullbackObjObjπ (pullback.fst p g) pointedSpaceProjection r
    have := InnerFibration.mem (q := (pre g).app SpaceInfinity) i hi
    have := InnerFibration.mem (q := r.π) i hi
    exact hasLiftingProperty_transportSquareRestriction p g i r

end SerrePositivity.InfinityCategories
