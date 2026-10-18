module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# 単射を経由する基底射の引き戻し

概要：単射 A→B を経由する T→B を A へ引き戻すと T に戻る。
方針：単射性で二つの A への射を等置し、恒等射と指定された T→A から逆を作る。
規約：Segal 1974 Lemma 1.7 の部分切断による厳密化の補助。
使われ方：単射上の部分切断の制限の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：単射を経由する基底射の引き戻しでは、第二射影は第一射影と指定射の合成に一致する。
方針：単射との後合成で引き戻しの可換性へ帰着する。
規約：基底射は s≫p である。
使われ方：引き戻しから元の対象への第一射影の逆。
-/
@[reassoc] theorem monoBasePullback_fst_snd {T A B : SSet.{u}}
    (p : A ⟶ B) [Mono p] (s : T ⟶ A) :
    pullback.fst (s ≫ p) p ≫ s = pullback.snd (s ≫ p) p := by
  apply (cancel_mono p).mp
  rw [Category.assoc]
  exact pullback.condition

/--
概要：単射を経由する基底射の引き戻しと、元の対象の標準同型。
方針：第一射影を同型の順方向に取り、恒等射と指定射の持ち上げを逆にする。
規約：同型の定義域は T×_B A、終域は T。
使われ方：右随伴から戻した切断の一意性。
-/
def monoBasePullbackIso {T A B : SSet.{u}} (p : A ⟶ B) [Mono p] (s : T ⟶ A) :
    pullback (s ≫ p) p ≅ T where
  hom := pullback.fst (s ≫ p) p
  inv := pullback.lift (𝟙 T) s (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp, monoBasePullback_fst_snd]
  inv_hom_id := pullback.lift_fst ..

/--
概要：標準同型の逆と第二射影の合成は指定射である。
方針：引き戻しへの持ち上げの第二射影の式を使う。
規約：逆は恒等射と s の持ち上げ。
使われ方：制限した部分切断から元の全空間へ戻した射の基底条件。
-/
@[reassoc] theorem monoBasePullbackIso_inv_snd {T A B : SSet.{u}}
    (p : A ⟶ B) [Mono p] (s : T ⟶ A) :
    (monoBasePullbackIso p s).inv ≫ pullback.snd (s ≫ p) p = s := pullback.lift_snd ..

end SerrePositivity.KST.Comparison
