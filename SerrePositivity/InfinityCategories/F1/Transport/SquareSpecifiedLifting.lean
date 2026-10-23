module

public import SerrePositivity.InfinityCategories.F1.Transport.SquareLifting

/-!
概要：分類図式の延長を指定した四角形の相対持ち上げ。
方針：指定図式を底とする相対内部 Hom の持ち上げだけを行う。
規約：先に選んだ分類図式を変更しない。
使われ方：Kerodon Lemma 5.6.8.10、可逆な分類図式の辺に沿う全空間側の延長。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：指定した分類図式を厳密に被覆する四角形の持ち上げ。
方針：境界の pointed space 値図式と指定分類図式を相対内部 Hom の底にまとめる。
規約：入力の分類図式を同型な別のものへ置き換えない。
使われ方：Kerodon Lemma 5.6.8.10、一次の可逆な辺の持ち上げの全空間側。 -/
lemma exists_transportSquareLift_with_diagram {E B D T U : SSet.{u + 1}}
    (p : E ⟶ B) (g : D ⟶ B) (i : T ⟶ U)
    (a : T ⟶ transportSquareSpace p) (b : U ⟶ transportSquareSpace (pullback.snd p g))
    (sq : CommSq a i (transportSquareRestriction p g) b)
    (F : U ⟶ (ihom B).obj SpaceInfinity.{u})
    (hF₀ : i ≫ F = a ≫ transportSquareDiagram p)
    (hFg : F ≫ (pre g).app SpaceInfinity = b ≫ transportSquareDiagram (pullback.snd p g))
    (r : internalHom.PullbackObjObj (pullback.fst p g) pointedSpaceProjection)
    [HasLiftingProperty i r.π] :
    ∃ L : U ⟶ transportSquareSpace p, i ≫ L = a ∧ L ≫ transportSquareRestriction p g = b ∧
      L ≫ transportSquareDiagram p = F := by
  let P := transportSquarePointed p
  let Q := transportSquareDiagram p
  let P₀ := transportSquarePointed (pullback.snd p g)
  let Q₀ := transportSquareDiagram (pullback.snd p g)
  have hP : a ≫ P ≫ (pre (pullback.fst p g)).app PointedSpaceInfinity = i ≫ b ≫ P₀ := by
    dsimp only [P, P₀]
    rw [← transportSquareRestriction_pointed, ← Category.assoc, sq.w, Category.assoc]
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
      dsimp only [P]
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
  refine ⟨L, ?_, ?_, hLQ⟩
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

end SerrePositivity.InfinityCategories
