module
public import SerrePositivity.KST.SConstruction.SplitBasePullbackIso
public import SerrePositivity.KST.Comparison.FibrantSquareCriterion

/-! # 連結基底上の切断四角形から退縮四角形への検出
概要：Kan fibration の可換な切断・退縮で、切断の四角形が homotopy pullback なら退縮もそうなる。
方針：退縮の厳密な fiber 比較を切断へ引き戻すと既証の切断比較の逆となり、連結基底で検出する。
規約：基底の連結性と非空な切断元を明示する。使われ方：σ₀ の面条件から δ₀ へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits HomotopicalAlgebra SSet
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel SerrePositivity.KST.Comparison
open scoped Simplicial

/-- 連結な Kan 基底上の fibration の切断が homotopy pullback を与えれば、その退縮もそうなる。 -/
lemma homotopyPullback_retraction_of_section {E B E' B' : SSet.{u}}
    [KanComplex B'] [SSet.IsPreconnected B']
    (p : E ⟶ B) (hp : J.rlp p) (p' : E' ⟶ B') (hp' : J.rlp p')
    (u : E ⟶ E') (v : B ⟶ B') (r : E' ⟶ E) (s : B' ⟶ B)
    (hu : u ≫ p' = p ≫ v) (hr : r ≫ p = p' ≫ s)
    (hur : u ≫ r = 𝟙 E) (hvs : v ≫ s = 𝟙 B) (b : B _⦋0⦌)
    (hsec : IsHomotopyPullback (CommSq.mk hu)) :
    IsHomotopyPullback (CommSq.mk hr) := by
  let Q := AnodyneHomotopy.anodyneQ
  let X : Over B' := Over.mk p'
  let Y : Over B' := Over.mk (pullback.fst s p)
  let c : E' ⟶ pullback s p := pullback.lift p' r hr.symm
  let f : X ⟶ Y := Over.homMk c (pullback.lift_fst ..)
  let a : E ⟶ pullback p' v := pullback.lift u p hu
  have ha : IsIso (Q.map a) := by
    have hc := (isHomotopyPullback_iff_strict_of_left_fibration (CommSq.mk hu) hp').mp hsec
    have he : a = (pullback.lift p u hu.symm : E ⟶ pullback v p') ≫
        (pullbackSymmetry v p').hom := by
      apply pullback.hom_ext
      · simp only [a, Category.assoc, pullbackSymmetry_hom_comp_fst,
          pullback.lift_snd, pullback.lift_fst]
      · simp only [a, Category.assoc, pullbackSymmetry_hom_comp_snd,
          pullback.lift_fst, pullback.lift_snd]
    rw [he, Q.map_comp]
    infer_instance
  let m : pullback p' v ⟶ pullback (pullback.fst s p) v := (sliceFiberFunctor v).map f
  have hmf : m ≫ pullback.fst (pullback.fst s p) v = pullback.fst p' v ≫ c :=
    sliceFiberFunctor_map_fst v f
  have hms : m ≫ pullback.snd (pullback.fst s p) v = pullback.snd p' v :=
    sliceFiberFunctor_map_snd v f
  have he : a ≫ m = (splitBasePullbackIso p v s hvs).inv := by
    dsimp only [splitBasePullbackIso]
    apply pullback.hom_ext
    · rw [Category.assoc, hmf, ← Category.assoc, pullback.lift_fst]
      apply pullback.hom_ext
      · simp only [c, Category.assoc, pullback.lift_fst]
        exact hu
      · simp only [c, Category.assoc, pullback.lift_snd, pullback.lift_fst]
        exact hur
    · rw [Category.assoc, hms, pullback.lift_snd]
      exact (pullback.lift_snd ..).symm
  have hm : IsIso (Q.map m) := by
    have ham : IsIso (Q.map a ≫ Q.map m) := by
      rw [← Q.map_comp, he]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp ham
  have hc : IsIso (Q.map c) := localized_isIso_of_connected_baseChange v b f hp'
    (J.rlp.pullback_fst s p hp) hm
  exact (isHomotopyPullback_iff_strict_of_left_fibration (CommSq.mk hr) hp).mpr hc

end SerrePositivity.KST.SConstruction
