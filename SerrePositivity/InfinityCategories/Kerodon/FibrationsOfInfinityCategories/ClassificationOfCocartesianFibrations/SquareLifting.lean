module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftAnodynePushoutProduct

/-!
概要：四角形の空間の制限に対する相対持ち上げ。
方針：分類図式を先に延長し、pointed space 側を相対内部 Hom の持ち上げで延長する。
規約：二つの延長は同じ底の図式を厳密に被覆する。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK）、制限写像の持ち上げ性の分解。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：四角形の制限の持ち上げは分類図式と相対内部 Hom の二つの持ち上げから得られる。
方針：分類図式を延長し、その図式を底とする pointed space 値の族を延長する。
規約：持ち上げる射 i は任意で、ホーンへの制限は不要。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK）、制限の相対充填の共通部分。 -/
lemma hasLiftingProperty_transportSquareRestriction {E B D T U : SSet.{u + 1}}
    (p : E ⟶ B) (g : D ⟶ B) (i : T ⟶ U)
    (r : internalHom.PullbackObjObj (pullback.fst p g) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection)
    [HasLiftingProperty i ((pre g).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})] [HasLiftingProperty i r.π] :
    HasLiftingProperty i (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction p g) := by
  constructor
  intro a b sq
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed p
  let Q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p
  let P₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (pullback.snd p g)
  let Q₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (pullback.snd p g)
  have hP : a ≫ P ≫ (pre (pullback.fst p g)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity = i ≫ b ≫ P₀ := by
    dsimp only [P, P₀]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction_pointed, ← Category.assoc,
      sq.w, Category.assoc]
  have hQ : a ≫ Q ≫ (pre g).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity = i ≫ b ≫ Q₀ := by
    dsimp only [Q, Q₀]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction_diagram, ← Category.assoc,
      sq.w, Category.assoc]
  let sqQ : CommSq (a ≫ Q) i ((pre g).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity) (b ≫ Q₀) := ⟨by
    simpa only [Category.assoc] using hQ⟩
  let F := sqQ.lift
  have hF₀ : i ≫ F = a ≫ Q := sqQ.fac_left
  have hFg : F ≫ (pre g).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity = b ≫ Q₀ := sqQ.fac_right
  have hbase : (b ≫ P₀) ≫ (ihom (pullback p g)).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (F ≫ (pre p).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity) ≫ (pre (pullback.fst p g)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace_condition]
    rw [Category.assoc, ← NatTrans.comp_app, ← pre_map, pullback.condition,
      pre_map, NatTrans.comp_app, ← Category.assoc F, hFg, Category.assoc]
  let V := r.isPullback.lift (b ≫ P₀) (F ≫ (pre p).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity) hbase
  have hVfst : V ≫ r.fst = b ≫ P₀ := r.isPullback.lift_fst _ _ _
  have hVsnd : V ≫ r.snd = F ≫ (pre p).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity := r.isPullback.lift_snd _ _ _
  let sqP : CommSq (a ≫ P) i r.π V := ⟨by
    apply r.hom_ext
    · simp only [Category.assoc, r.π_fst, hVfst]
      exact hP
    · simp only [Category.assoc, r.π_snd, hVsnd]
      change a ≫ P ≫ (ihom E).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = i ≫ F ≫ (pre p).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity
      dsimp only [P, Q] at hF₀ ⊢
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace_condition, ← Category.assoc i, hF₀, Category.assoc]⟩
  let H := sqP.lift
  have hHbase : H ≫ (ihom E).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = F ≫ (pre p).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity := by
    calc
      _ = (H ≫ r.π) ≫ r.snd := by rw [Category.assoc, r.π_snd]; rfl
      _ = _ := (congrArg (fun f ↦ f ≫ r.snd) sqP.fac_right).trans hVsnd
  have hHrest : H ≫ (pre (pullback.fst p g)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity = b ≫ P₀ := by
    calc
      _ = (H ≫ r.π) ≫ r.fst := by rw [Category.assoc, r.π_fst]; rfl
      _ = _ := (congrArg (fun f ↦ f ≫ r.fst) sqP.fac_right).trans hVfst
  let L : U ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p := pullback.lift H F hHbase
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
    · change L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction p g ≫ P₀ = b ≫ P₀
      dsimp only [P₀]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction_pointed, ← Category.assoc]
      change (L ≫ P) ≫ _ = _
      rw [hLP]
      exact hHrest
    · change L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction p g ≫ Q₀ = b ≫ Q₀
      dsimp only [Q₀]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction_diagram, ← Category.assoc]
      change (L ≫ Q) ≫ _ = _
      rw [hLQ]
      exact hFg

/-- 概要：単射な底の制限は四角形の空間の inner fibration を与える。
方針：分類図式の制限の inner fibration と相対内部 Hom の left fibration を使う。
規約：p の fibration 性を要求せず、表現条件の部分空間の持ち上げ性は別に検証する。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK）、周囲の四角形の制限の内ホーン充填。 -/
instance transportSquareRestriction_innerFibration {E B D : SSet.{u + 1}}
    (p : E ⟶ B) (g : D ⟶ B) [Mono g] : InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction p g) where
  mem := by
    intro T U i hi
    let r := Functor.PullbackObjObj.ofHasPullback internalHom
      (pullback.fst p g) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration r.π :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_pullbackObjObjπ (pullback.fst p g) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection r
    have := InnerFibration.mem (q := (pre g).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity) i hi
    have := InnerFibration.mem (q := r.π) i hi
    exact hasLiftingProperty_transportSquareRestriction p g i r

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
