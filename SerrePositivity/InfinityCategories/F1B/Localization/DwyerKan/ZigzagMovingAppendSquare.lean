module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingAppendLaws

/-!
# 動く接合点を持つ可換四角形の貼り合わせ

概要：二つの全頂点で可換な比較を、同じ接合点で貼る。
方針：元の Moving.map の合成則と両方の自然性を使う。
規約：四隅の局所端点も動く。
使われ方：相対自然変換と外側の二列の自然性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend.Moving
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : Word} {X₀ Y₀ Z₀ X₁ Y₁ Z₁ X₀' Y₀' Z₀' X₁' Y₁' Z₁' : C}
  {S₀ : Zigzag W a X₀ Y₀} {S₁ : Zigzag W a X₁ Y₁}
  {S₀' : Zigzag W a X₀' Y₀'} {S₁' : Zigzag W a X₁' Y₁'}
  {T₀ : Zigzag W b Y₀ Z₀} {T₁ : Zigzag W b Y₁ Z₁}
  {T₀' : Zigzag W b Y₀' Z₀'} {T₁' : Zigzag W b Y₁' Z₁'}

lemma map_square (f : Zigzag.MovingHom S₀ S₁) (g : Zigzag.MovingHom T₀ T₁)
    (f' : Zigzag.MovingHom S₀' S₁') (g' : Zigzag.MovingHom T₀' T₁')
    (α₀ : Zigzag.MovingHom S₀ S₀') (β₀ : Zigzag.MovingHom T₀ T₀')
    (α₁ : Zigzag.MovingHom S₁ S₁') (β₁ : Zigzag.MovingHom T₁ T₁')
    (hj : HEq (f.app (Fin.last a.length)) (g.app 0))
    (hj' : HEq (f'.app (Fin.last a.length)) (g'.app 0))
    (hα₀ : HEq (α₀.app (Fin.last a.length)) (β₀.app 0))
    (hα₁ : HEq (α₁.app (Fin.last a.length)) (β₁.app 0))
    (hs : f.comp α₁ = α₀.comp f') (ht : g.comp β₁ = β₀.comp g') :
    (map f g hj).comp (map α₁ β₁ hα₁) =
      (map α₀ β₀ hα₀).comp (map f' g' hj') := by
  have hc : HEq ((f.comp α₁).app (Fin.last a.length)) ((g.comp β₁).app 0) :=
    heq_comp (S₀.last.trans T₀.first.symm) (S₁.last.trans T₁.first.symm)
      (S₁'.last.trans T₁'.first.symm) hj hα₁
  have hc' : HEq ((α₀.comp f').app (Fin.last a.length)) ((β₀.comp g').app 0) := by
    rw [← hs, ← ht]
    exact hc
  calc
    _ = map (f.comp α₁) (g.comp β₁) hc := map_comp f g α₁ β₁ hj hα₁ hc
    _ = map (α₀.comp f') (β₀.comp g') hc' := by
      apply Zigzag.MovingHom.ext
      intro k
      exact congrArg₂ (fun l r => app l r k) hs ht
    _ = _ := (map_comp α₀ β₀ f' g' hα₀ hj' hc').symm

end SerrePositivity.EInfinity.Hammock.ZigzagAppend.Moving
