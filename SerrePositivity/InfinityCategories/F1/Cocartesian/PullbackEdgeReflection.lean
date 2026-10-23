module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackSquareComparison

/-!
概要：任意の単体集合への底変換で、元の cocartesian 辺を保存・反映する。
方針：指定辺をその底の標準区間へ引き戻し、貼り合わせた pullback に前の判定を適用する。
規約：新しい底の quasicategory 性を要求しない。
使われ方：境界・セルへの引き戻しで元の指定辺の保存と被覆を検証する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 任意の底への pullback の cocartesian 辺の像は、元の fibration の cocartesian 辺。 -/
lemma isCocartesianEdge_image_of_isPullback {P E A B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] {i : P ⟶ E} {r : P ⟶ A} {f : A ⟶ B}
    (hs : IsPullback i r p f) (e : P _⦋1⦌) (he : IsCocartesianEdge r e) :
    IsCocartesianEdge p (i.app (Opposite.op ⦋1⦌) e) := by
  let t : (Δ[1] : SSet.{u}) ⟶ P := SSet.yonedaEquiv.symm e
  let b := t ≫ r
  let l : (Δ[1] : SSet.{u}) ⟶ pullback r b := pullback.lift t (𝟙 _) (by simp [b])
  let a := SSet.yonedaEquiv l
  have hla : (pullback.fst r b).app (Opposite.op ⦋1⦌) a = e := by
    rw [← SSet.yonedaEquiv_comp, pullback.lift_fst]
    exact SSet.yonedaEquiv.apply_symm_apply e
  have hco : IsCocartesianEdge (pullback.snd r b) a :=
    isCocartesianEdge_pullback r b a (by rw [hla]; exact he)
  have hsc : IsPullback (pullback.fst r b ≫ i) (pullback.snd r b) p (b ≫ f) :=
    (IsPullback.of_hasPullback r b).paste_horiz hs
  have h := isCocartesianEdge_image_of_isPullback_of_quasicategory_base p hsc a hco
  change IsCocartesianEdge p
    (i.app (Opposite.op ⦋1⦌) ((pullback.fst r b).app (Opposite.op ⦋1⦌) a)) at h
  rwa [hla] at h

/-- 元の cocartesian 性は、任意の底への実際の pullback 表示で厳密に一致する。 -/
lemma isCocartesianEdge_isPullback_iff {P E A B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] {i : P ⟶ E} {r : P ⟶ A} {f : A ⟶ B}
    (hs : IsPullback i r p f) (e : P _⦋1⦌) :
    IsCocartesianEdge r e ↔ IsCocartesianEdge p (i.app (Opposite.op ⦋1⦌) e) :=
  ⟨isCocartesianEdge_image_of_isPullback p hs e, kanIsCocartesianEdge_isPullback hs e⟩

/-- 標準 pullback の第一射影によって、任意の底でも cocartesian 性を検出できる。 -/
lemma isCocartesianEdge_pullback_iff {E A B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (f : A ⟶ B) (e : (pullback p f) _⦋1⦌) :
    IsCocartesianEdge (pullback.snd p f) e ↔
      IsCocartesianEdge p ((pullback.fst p f).app (Opposite.op ⦋1⦌) e) :=
  isCocartesianEdge_isPullback_iff p (IsPullback.of_hasPullback p f) e

end SerrePositivity.InfinityCategories
