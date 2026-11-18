module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCoverGraphValue

/-!
# 元の graph の値の fiber と全部分圏の nerve

概要：元の固定語の値の fiber は元の値を固定した zigzag 圏の nerve である。
方針：同じ単体の全行の値の一致から全部分圏へ持ち上げる。
規約：元の全行・縦射・単体作用素を保持する。
使われ方：元の全語の fiber の図式とその余極限。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover
open _root_.CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y)

def fiberGraphInclusion (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberGraphDiagram A Y β).obj w ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.space (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphValue A Y w) β where
  app _ := ↾fun τ => ⟨τ ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A w Y β).ι, (τ.obj 0).property⟩
  naturality n m θ := by
    ext τ
    apply Subtype.ext
    rfl

def graphFiberLift {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {n : SimplexCategoryᵒᵖ}
    (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.space (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphValue A Y w) β).obj n) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberGraphDiagram A Y β).obj w).obj n where
  obj k := ⟨τ.val.obj k,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_eq _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top
      (τ.val.map (homOfLE (Fin.zero_le k)))).symm.trans τ.property⟩
  map f := ObjectProperty.homMk (τ.val.map f)
  map_id k := ObjectProperty.hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A w Y β) (τ.val.map_id k)
  map_comp f g := ObjectProperty.hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A w Y β) (τ.val.map_comp f g)

lemma graphFiberLift_projection {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {n : SimplexCategoryᵒᵖ}
    (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.space (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphValue A Y w) β).obj n) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphFiberLift A Y β τ ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A w Y β).ι = τ.val := by
  apply CategoryTheory.Functor.hext
    (F := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphFiberLift A Y β τ ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A w Y β).ι) (G := τ.val)
  · intro k
    rfl
  · intro j k f
    rfl

lemma fiberGraphInclusion_bijective (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (n : SimplexCategoryᵒᵖ) :
    Function.Bijective ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.fiberGraphInclusion A Y β w).app n) := by
  constructor
  · intro τ σ h
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.valueFiberFunctor_ext A τ σ (congrArg Subtype.val h)
  · intro τ
    exact ⟨_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphFiberLift A Y β τ, Subtype.ext (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphFiberLift_projection A Y β τ)⟩

def fiberGraphIso (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberGraphDiagram A Y β).obj w ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.space (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.graphValue A Y w) β :=
  NatIso.ofComponents
    (fun n => (Equiv.ofBijective ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.fiberGraphInclusion A Y β w).app n)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.fiberGraphInclusion_bijective A Y β w n)).toIso)
    (fun θ => (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.fiberGraphInclusion A Y β w).naturality θ)

lemma fiberGraphIso_hom (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.fiberGraphIso A Y β w).hom = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover.fiberGraphInclusion A Y β w :=
  rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FreeQuiverCover
