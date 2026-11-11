module

public import SerrePositivity.EInfinity.Hammock.TwoSidedThomasonBaseChange
public import SerrePositivity.EInfinity.FrameHom.ThomasonNerveMap

/-!
# 元の二方向比較から一方向 Thomason 比較への回収

概要：元の左ラベルを忘れると、元の一方向 bar と同じ Thomason 比較射に戻る。
方針：全射の底と右成分だけを保持する忘却を各次数で nerve と対角へ送る。
規約：既存の一方向 bar・比較射を再実装せず、同じ射との可換式を示す。
使われ方：DK9.5の二方向比較の弱同値性への帰着。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedThomason
open CategoryTheory Opposite
open SerrePositivity.SimplicialModel

variable {W : Type u} [Category.{u} W]

def forgetLeftElements (F : Wᵒᵖ ⥤ Type u) (G : W ⥤ Type u) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element F G ⥤ G.Elements where
  obj X := G.elementsMk X.base X.right
  map f := Functor.Elements.homMk f.base f.right
  map_id _ := Functor.Elements.hom_ext rfl
  map_comp _ _ := Functor.Elements.hom_ext rfl

lemma forgetLeftElements_naturality {F F' : Wᵒᵖ ⥤ Type u} {G G' : W ⥤ Type u}
    (α : F ⟶ F') (β : G ⟶ G') :
    forgetLeftElements F G ⋙ β.mapElements =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map α β ⋙ forgetLeftElements F' G' := rfl

def forgetLeftRows (F : Wᵒᵖ ⥤ SSet.{u}) (G : W ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rows F G ⟶ (BarConstruction.rows W).obj G where
  app n := nerveMap (forgetLeftElements (F.flip.obj n) (G.flip.obj n))
  naturality {n m} θ := by
    ext k e
    exact congrArg (fun J => e ⋙ J)
      (forgetLeftElements_naturality (F.flip.map θ) (G.flip.map θ)).symm

def forgetLeftBar (F : Wᵒᵖ ⥤ SSet.{u}) (G : W ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.space F G ⟶ (BarConstruction.functor W).obj G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map (forgetLeftRows F G)

variable (F : Wᵒᵖ ⥤ Cat.{u, u}) (G : W ⥤ Cat.{u, u})

def forgetLeftTotal : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G ⥤ Grothendieck G :=
  Grothendieck.pre G (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.contravariantProjection F)

lemma simplex_forgetLeft {n : ℕ} (e : ComposableArrows (labels F G n) n) :
    simplex F G e ⋙ forgetLeftTotal F G =
      FrameHom.Thomason.simplex G (e ⋙ forgetLeftElements
        (FrameHom.Thomason.values F n) (FrameHom.Thomason.values G n)) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

lemma map_forgetLeft :
    map F G ≫ nerveMap (forgetLeftTotal F G) =
      forgetLeftBar (F ⋙ nerveFunctor) (G ⋙ nerveFunctor) ≫ FrameHom.Thomason.map G := by
  ext n e
  exact simplex_forgetLeft F G e

end SerrePositivity.EInfinity.Hammock.TwoSidedThomason
