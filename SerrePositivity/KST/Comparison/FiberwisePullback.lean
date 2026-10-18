module

public import SerrePositivity.KST.Comparison.FiberwiseAnodyne
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# 基底上のホモトピーの引き戻し

概要：基底を固定する写像と実ホモトピーを、任意の射に沿って引き戻す。
方針：二つの射影を用いて写像と区間の族を引き戻しへ持ち上げる。
規約：Segal 1974 Proposition 1.6・Lemma 1.7 の基底付き比較。
使われ方：Kan 分解のファイバーごとの収縮と局所化同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：基底を固定する自己写像を任意の引き戻しへ移す。
方針：第一射影を保ち、第二射影へ自己写像を後合成する。
規約：Segal 1974 Lemma 1.7 の基底上の射。
使われ方：基底上の収縮をファイバーへ制限する。
-/
def pullbackMapOver {T X B : SSet.{u}} (p : T ⟶ B) (k : X ⟶ B)
    (s : T ⟶ T) (hs : s ≫ p = p) : pullback k p ⟶ pullback k p :=
  pullback.lift (pullback.fst k p) (pullback.snd k p ≫ s) (by
    rw [Category.assoc, hs]
    exact pullback.condition)

/--
概要：引き戻した自己写像の第一射影は元の第一射影である。
方針：持ち上げの計算則を使う。
規約：Segal 1974 Lemma 1.7。
使われ方：基底上のホモトピーの端点条件。
-/
@[reassoc] theorem pullbackMapOver_fst {T X B : SSet.{u}} (p : T ⟶ B) (k : X ⟶ B)
    (s : T ⟶ T) (hs : s ≫ p = p) :
    pullbackMapOver p k s hs ≫ pullback.fst k p = pullback.fst k p := pullback.lift_fst ..

/--
概要：引き戻した自己写像の第二射影は元の自己写像との合成である。
方針：持ち上げの計算則を使う。
規約：Segal 1974 Lemma 1.7。
使われ方：引き戻し上の端点の同定。
-/
@[reassoc] theorem pullbackMapOver_snd {T X B : SSet.{u}} (p : T ⟶ B) (k : X ⟶ B)
    (s : T ⟶ T) (hs : s ≫ p = p) :
    pullbackMapOver p k s hs ≫ pullback.snd k p = pullback.snd k p ≫ s := pullback.lift_snd ..

/--
概要：恒等写像を引き戻すと恒等写像になる。
方針：二つの射影で比較する。
規約：Segal 1974 Lemma 1.7 の引き戻しの規約。
使われ方：収縮の端点を恒等写像として同定する。
-/
theorem pullbackMapOver_id {T X B : SSet.{u}} (p : T ⟶ B) (k : X ⟶ B) :
    pullbackMapOver p k (𝟙 T) (Category.id_comp p) = 𝟙 (pullback k p) := by
  apply pullback.hom_ext
  · rw [pullbackMapOver_fst, Category.id_comp]
  · rw [pullbackMapOver_snd, Category.comp_id, Category.id_comp]

/--
概要：基底を固定する実ホモトピーを任意の引き戻しへ移す。
方針：区間の族の第一射影を固定し、第二射影を元のホモトピーへ送る。
規約：Segal 1974 Lemma 1.7。基底上の等式を区間全体で要求する。
使われ方：anodyne 分解の相対収縮を厳密ファイバーへ制限する。
-/
def pullbackHomotopyOver {T X B : SSet.{u}} (p : T ⟶ B) (k : X ⟶ B)
    {f g : T ⟶ T} (hf : f ≫ p = p) (hg : g ≫ p = p) (H : SSet.Homotopy f g)
    (hH : H.h ≫ p = fst T (Δ[1] : SSet.{u}) ≫ p) :
    SSet.Homotopy (pullbackMapOver p k f hf) (pullbackMapOver p k g hg) := by
  let a := fst (pullback k p) (Δ[1] : SSet.{u}) ≫ pullback.fst k p
  let b := pullback.snd k p ▷ (Δ[1] : SSet.{u}) ≫ H.h
  have hab : a ≫ k = b ≫ p := by
    dsimp only [a, b]
    rw [Category.assoc, pullback.condition, Category.assoc, hH]
    exact (whiskerRight_fst_assoc (pullback.snd k p) _ p).symm
  let h := pullback.lift a b hab
  refine { h := h, h₀ := ?_, h₁ := ?_, rel := ?_ }
  · change SSet.ι₀ ≫ h = pullbackMapOver p k f hf
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullbackMapOver_fst]
      rfl
    · rw [Category.assoc, pullback.lift_snd, pullbackMapOver_snd]
      dsimp only [b]
      rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, H.h₀]
  · change SSet.ι₁ ≫ h = pullbackMapOver p k g hg
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullbackMapOver_fst]
      rfl
    · rw [Category.assoc, pullback.lift_snd, pullbackMapOver_snd]
      dsimp only [b]
      rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, H.h₁]
  · apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.KST.Comparison
