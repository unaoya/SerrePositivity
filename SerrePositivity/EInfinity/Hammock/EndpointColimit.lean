module

public import SerrePositivity.EInfinity.Hammock.ColimitGraph
public import SerrePositivity.EInfinity.Hammock.ZigzagEndpointChange

/-!
# 元の hammock 余極限と端点表示の変更

概要：端点の等式による同じ hammock 余極限の移送と元の標準射の整合を証明する。
方針：端点の等式で帰納し、元の恒等射・標準余錐の自然性を使う。
規約：同型の選択や弱比較を仮定しない。
使われ方：切断因子の元の標準射の像の一致。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.EndpointChange
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X X' Y Y' : C}

def colimitMap (hX : X = X') (hY : Y = Y') :
    colimitGraph W X Y ⟶ colimitGraph W X' Y' :=
  eqToHom (by cases hX; cases hY; rfl)

lemma inclusion (hX : X = X') (hY : Y = Y') (w : Word) :
    nerveMap (Zigzag.EndpointChange.functor (W := W) (w := w) hX hY) ≫
      graphInclusion W X' Y' w = graphInclusion W X Y w ≫ colimitMap W hX hY := by
  cases hX
  cases hY
  rw [Zigzag.EndpointChange.functor_refl]
  have hid : nerveMap (𝟭 (Zigzag W w X Y)) = 𝟙 _ := by
    ext n F
    exact Functor.comp_id F
  rw [hid]
  simp only [colimitMap, eqToHom_refl, Category.id_comp, Category.comp_id]

lemma image_eq {a b : Word} (f : a ⟶ b) (hX : X = X') (hY : Y = Y')
    {n : SimplexCategoryᵒᵖ} (S : (graph W a X Y).obj n) (T : (graph W b X' Y').obj n)
    (hST : S ⋙ WordAction.functor f ⋙ Zigzag.EndpointChange.functor hX hY = T) :
    (colimitMap W hX hY).app n ((graphInclusion W X Y a).app n S) =
      (graphInclusion W X' Y' b).app n T := by
  have hι := congrArg (fun g => g.app n S) (graphInclusion_naturality W X Y f)
  have he := congrArg (fun g => g.app n (S ⋙ WordAction.functor f)) (inclusion W hX hY b)
  have ht := congrArg (fun z => (graphInclusion W X' Y' b).app n z) hST
  exact (congrArg (fun z => (colimitMap W hX hY).app n z) hι.symm).trans
    (he.symm.trans ht)

end SerrePositivity.EInfinity.Hammock.EndpointChange
