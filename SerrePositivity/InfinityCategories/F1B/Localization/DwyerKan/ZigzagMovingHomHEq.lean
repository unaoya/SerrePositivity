module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingAppendLaws
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordActionMovingMap
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordIdentity

/-!
# 動く縦比較の表示の異種等式

概要：同じ端点の行の等式と全成分の異種等式から比較全体を回収する。
方針：行の表示を等式で移し、元の全成分の外延性を使う。
規約：接合点の証明の選択には依存しない。
使われ方：元の語の作用と相対自然変換の比較の整合。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingHom
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : Word}
  {X Y Z X' Y' Z' : C}

lemma hext {S S' : Zigzag W a X Y} {T T' : Zigzag W a X' Y'}
    (hS : S = S') (hT : T = T') (f : MovingHom S T) (g : MovingHom S' T')
    (h : ∀ j, HEq (f.app j) (g.app j)) : HEq f g := by
  subst S'
  subst T'
  exact heq_of_eq (ext f g (fun j => eq_of_heq (h j)))

lemma app_heq_of_heq {S S' : Zigzag W a X Y} {T T' : Zigzag W a X' Y'}
    (hS : S = S') (hT : T = T') {f : MovingHom S T} {g : MovingHom S' T'}
    (h : HEq f g) (j : Fin (a.length + 1)) : HEq (f.app j) (g.app j) := by
  subst S'
  subst T'
  exact heq_of_eq (congrArg (fun k => k.app j) (eq_of_heq h))

lemma append_heq {S₀ S₀' : Zigzag W a X Y} {S₁ S₁' : Zigzag W a X' Y'}
    {T₀ T₀' : Zigzag W b Y Z} {T₁ T₁' : Zigzag W b Y' Z'}
    (hS₀ : S₀ = S₀') (hS₁ : S₁ = S₁') (hT₀ : T₀ = T₀') (hT₁ : T₁ = T₁')
    {f : MovingHom S₀ S₁} {f' : MovingHom S₀' S₁'}
    {g : MovingHom T₀ T₁} {g' : MovingHom T₀' T₁'} (hf : HEq f f') (hg : HEq g g')
    (hj : HEq (f.app (Fin.last a.length)) (g.app 0))
    (hj' : HEq (f'.app (Fin.last a.length)) (g'.app 0)) :
    HEq (ZigzagAppend.Moving.map f g hj) (ZigzagAppend.Moving.map f' g' hj') := by
  subst S₀'
  subst S₁'
  subst T₀'
  subst T₁'
  apply heq_of_eq
  apply ext
  intro j
  exact congrArg₂ (fun l r => ZigzagAppend.Moving.app l r j) (eq_of_heq hf) (eq_of_heq hg)

lemma wordAction_id_heq [W.IsMultiplicative] {S : Zigzag W a X Y} {T : Zigzag W a X' Y'}
    (f : MovingHom S T) : HEq (WordAction.movingMap (𝟙 a) f) f := by
  apply hext (WordAction.obj_id S) (WordAction.obj_id T)
  intro j
  exact app_heq f (Word.Hom.cut_id a j)

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingHom
