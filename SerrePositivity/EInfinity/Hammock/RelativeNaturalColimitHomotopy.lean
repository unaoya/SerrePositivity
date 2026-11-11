module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalWordHomotopy
public import SerrePositivity.EInfinity.Hammock.RelativeNaturalMapRecovery

/-!
# 元の全語の余極限上の相対自然変換のホモトピー

概要：post ηY ∘ H_F と pre ηX ∘ H_G を元の同じ区間で結ぶ。
方針：区間との積の余極限保存で降ろし、元の標準射上で両端を回収する。
規約：Word の filtered 性や単体集合のモデル構造を要求しない。
使われ方：端点移動を含む DK のホモトピー比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RelativeNatural
open CategoryTheory Limits MonoidalCategory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor)
  (hη : ∀ X, V (η.app X)) (X Y : C)

def intervalCocone : Cocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y ⋙
    tensorRight (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1))) where
  pt := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph V (F.functor.obj X) (G.functor.obj Y)
  ι :=
    { app w := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedWordHomotopy η hη w X Y).h
      naturality a b f := by
        change ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f ▷ _) ≫ _ = _ ≫ 𝟙 _
        simpa only [Category.comp_id] using _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedWordHomotopy_wordAction η hη X Y f }

def colimitHomotopyMap : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y ⊗
    SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph V (F.functor.obj X) (G.functor.obj Y) :=
  (isColimitOfPreserves (tensorRight (SSet.stdSimplex.obj (SimplexCategory.mk 1)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph_isColimit W X Y)).desc (intervalCocone η hη X Y)

lemma colimitHomotopyMap_fac (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w ▷ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)) ≫
      colimitHomotopyMap η hη X Y = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedWordHomotopy η hη w X Y).h :=
  (isColimitOfPreserves (tensorRight (SSet.stdSimplex.obj (SimplexCategory.mk 1)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph_isColimit W X Y)).fac (intervalCocone η hη X Y) w

lemma colimitHomotopyMap_zero : SSet.ι₀ ≫ colimitHomotopyMap η hη X Y =
    Relative.colimitMap F X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap (F.functor.obj X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap V (η.app Y)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph_hom_ext W X Y
  intro w
  calc
    _ = SSet.ι₀ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w ▷ _) ≫ colimitHomotopyMap η hη X Y := by
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro σ
      rfl
    _ = SSet.ι₀ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedWordHomotopy η hη w X Y).h := by rw [colimitHomotopyMap_fac]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeMap η w X Y := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedWordHomotopy η hη w X Y).h₀
    _ = _ := beforeMap_recovery η w X Y

lemma colimitHomotopyMap_one : SSet.ι₁ ≫ colimitHomotopyMap η hη X Y =
    Relative.colimitMap G X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap V (η.app X)) (G.functor.obj Y) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph_hom_ext W X Y
  intro w
  calc
    _ = SSet.ι₁ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w ▷ _) ≫ colimitHomotopyMap η hη X Y := by
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro σ
      rfl
    _ = SSet.ι₁ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedWordHomotopy η hη w X Y).h := by rw [colimitHomotopyMap_fac]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterMap η w X Y := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedWordHomotopy η hη w X Y).h₁
    _ = _ := afterMap_recovery η w X Y

def homotopy : SSet.Homotopy
    (Relative.colimitMap F X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap (F.functor.obj X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap V (η.app Y)))
    (Relative.colimitMap G X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap V (η.app X)) (G.functor.obj Y)) where
  h := colimitHomotopyMap η hη X Y
  h₀ := colimitHomotopyMap_zero η hη X Y
  h₁ := colimitHomotopyMap_one η hη X Y
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.EInfinity.Hammock.RelativeNatural
