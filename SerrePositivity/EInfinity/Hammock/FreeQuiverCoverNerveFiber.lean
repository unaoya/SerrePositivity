module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverGraphValue

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
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y)

def fiberGraphInclusion (w : Word) : (fiberGraphDiagram A Y β).obj w ⟶
    SimplicialValueFiber.space (graphValue A Y w) β where
  app _ := ↾fun τ => ⟨τ ⋙ (zigzagValueProperty A w Y β).ι, (τ.obj 0).property⟩
  naturality n m θ := by
    ext τ
    apply Subtype.ext
    rfl

def graphFiberLift {w : Word} {n : SimplexCategoryᵒᵖ}
    (τ : (SimplicialValueFiber.space (graphValue A Y w) β).obj n) :
    ((fiberGraphDiagram A Y β).obj w).obj n where
  obj k := ⟨τ.val.obj k,
    (Zigzag.Value.value_eq positiveEvaluation positiveEvaluation_inverts_top
      (τ.val.map (homOfLE (Fin.zero_le k)))).symm.trans τ.property⟩
  map f := ObjectProperty.homMk (τ.val.map f)
  map_id k := ObjectProperty.hom_ext (zigzagValueProperty A w Y β) (τ.val.map_id k)
  map_comp f g := ObjectProperty.hom_ext (zigzagValueProperty A w Y β) (τ.val.map_comp f g)

lemma graphFiberLift_projection {w : Word} {n : SimplexCategoryᵒᵖ}
    (τ : (SimplicialValueFiber.space (graphValue A Y w) β).obj n) :
    graphFiberLift A Y β τ ⋙ (zigzagValueProperty A w Y β).ι = τ.val := by
  apply CategoryTheory.Functor.hext
    (F := graphFiberLift A Y β τ ⋙ (zigzagValueProperty A w Y β).ι) (G := τ.val)
  · intro k
    rfl
  · intro j k f
    rfl

lemma fiberGraphInclusion_bijective (w : Word) (n : SimplexCategoryᵒᵖ) :
    Function.Bijective ((fiberGraphInclusion A Y β w).app n) := by
  constructor
  · intro τ σ h
    exact valueFiberFunctor_ext A τ σ (congrArg Subtype.val h)
  · intro τ
    exact ⟨graphFiberLift A Y β τ, Subtype.ext (graphFiberLift_projection A Y β τ)⟩

def fiberGraphIso (w : Word) : (fiberGraphDiagram A Y β).obj w ≅
    SimplicialValueFiber.space (graphValue A Y w) β :=
  NatIso.ofComponents
    (fun n => (Equiv.ofBijective ((fiberGraphInclusion A Y β w).app n)
      (fiberGraphInclusion_bijective A Y β w n)).toIso)
    (fun θ => (fiberGraphInclusion A Y β w).naturality θ)

lemma fiberGraphIso_hom (w : Word) : (fiberGraphIso A Y β w).hom = fiberGraphInclusion A Y β w :=
  rfl

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
