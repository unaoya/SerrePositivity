module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeUpperDiagram

/-!
# 元の augmentation による始域比較の全自然変換

概要：同じ四列の上下の図式を元の augmentation の全成分で結ぶ。
方針：元の自然性を各頂点の正方形に代入する。
規約：元の始域射・全要素・全縦弱同値を保持する。
使われ方：source frame の始域自然性のホモトピー。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v uI vI
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {I : Type uI} [Category.{vI} I] {X' X Y : C}
  (U : I ⥤ C) (p : U ⟶ (Functor.const I).obj X) (hp : ∀ i, W (p.app i))
  (f : X' ⟶ X) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), W (U.map a))

def lowerDiagram : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.word X' Y where
  obj i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeObjects.lower W (p.app i) (hp i) f (σ.app i)
  map {i j} a :=
    { app := Fin.cases (𝟙 X') (Fin.cases (𝟙 X') (Fin.cases (𝟙 X)
        (Fin.cases (U.map a) (Fin.cases (𝟙 Y) (fun k => Fin.elim0 k)))))
      app_mem k := by
        fin_cases k
        · exact W.id_mem X'
        · exact W.id_mem X'
        · exact W.id_mem X
        · exact hU a
        · exact W.id_mem Y
      first := rfl
      last := rfl
      comm k := by
        fin_cases k
        · rfl
        · exact (Category.comp_id _).trans (Category.id_comp _).symm
        · exact (p.naturality a).symm
        · exact (σ.naturality a).symm }
  map_id i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (by
    intro k
    fin_cases k
    · rfl
    · rfl
    · rfl
    · exact U.map_id i
    · rfl)
  map_comp a b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (by
    intro k
    fin_cases k
    · exact (Category.id_comp _).symm
    · exact (Category.id_comp _).symm
    · exact (Category.id_comp _).symm
    · exact U.map_comp a b
    · exact (Category.id_comp _).symm)

variable (U' : I ⥤ C) (p' : U' ⟶ (Functor.const I).obj X') (hp' : ∀ i, W (p'.app i))
  (α : U' ⟶ U) (h : α ≫ p = p' ≫ (Functor.const I).map f)
  (hU' : ∀ {i j} (a : i ⟶ j), W (U'.map a))

def diagramComponent : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperDiagram W U' U p' hp' α σ hU' hU ⟶
    lowerDiagram W U p hp f σ hU where
  app i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeObjects.component W (p'.app i) (hp' i) (p.app i) (hp i) (α.app i) f (σ.app i)
    (NatTrans.congr_app h i)
  naturality i j a := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro k
    fin_cases k
    · rfl
    · exact p'.naturality a
    · exact p.naturality a
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
