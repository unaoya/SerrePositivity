module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofRightIdentity
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHom
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Category.ULift

/-!
# 元の frame Hom の全単体を二列 roof へ送る

概要：同じ augmentation と元の Hom 単体を X←Aⁿ→Y の二列にする。
方針：全単体作用素を同じ frame の射で送り、全縦弱同値を保持する。
規約：元の終域と全単体・全作用素を保持する。
使われ方：恒等右脚の比較の全両端点自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory Opposite
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y : C} (A : SimplexCategory ⥤ C) (p : A ⟶ (Functor.const SimplexCategory).obj X)
  (hp : ∀ n, W (p.app n)) (hA : ∀ {i j} (a : i ⟶ j), W (A.map a))

def frameLeftRoofFunctor : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y).Elements)ᵒᵖ ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word X Y where
  obj s := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W (p.app s.unop.obj.unop) (hp _) s.unop.val
  map {s t} a := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.map W
    (p := p.app s.unop.obj.unop) (q := p.app t.unop.obj.unop)
    (hp := hp s.unop.obj.unop) (hq := hp t.unop.obj.unop)
    (f := s.unop.val) (g := t.unop.val) (A.map a.unop.hom.unop) (hA _)
    (by
      have h := p.naturality a.unop.hom.unop
      change A.map a.unop.hom.unop ≫ p.app t.unop.obj.unop =
        p.app s.unop.obj.unop ≫ 𝟙 X at h
      exact h.trans (Category.comp_id _))
    a.unop.map_val.symm
  map_id s := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (by
    intro i
    fin_cases i
    · rfl
    · exact A.map_id _
    · rfl)
  map_comp a b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (by
    intro i
    fin_cases i
    · exact (Category.id_comp _).symm
    · exact A.map_comp a.unop.hom.unop b.unop.hom.unop
    · exact (Category.id_comp _).symm)

def frameLeftRoofNerveMap :
    nerve (ULiftHom.{max u v} (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y).Elements)ᵒᵖ) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word X Y where
  app _ := ↾fun σ => σ ⋙ ULiftHom.down.{0, v, max u v} ⋙ frameLeftRoofFunctor W A p hp hA
  naturality _ _ _ := rfl

end SerrePositivity.EInfinity.FrameHom
