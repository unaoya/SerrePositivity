module

public import SerrePositivity.EInfinity.Hammock.RootedFiniteGraphColimit
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RootedFiniteBidiagram

/-!
# 固定語の元の余極限同型の全語での自然性

概要：元の全標準射を回収する同型を Word の図式の自然同型へ束ねる。
方針：元の有限部分集合の標準射上で射影の全語の整合を検査する。
規約：元の全体の graph 図式へ同じ作用で戻る。
使われ方：二つの元の余極限の交換。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RootedFinite
open CategoryTheory Limits
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] (X Y : Q)

def graphColimitDiagramIso : graphWordDiagram T X Y ⋙ colim ≅
    Hammock.graphDiagram (⊤ : MorphismProperty (Paths Q))
      ((Paths.of Q).obj X) ((Paths.of Q).obj Y) :=
  NatIso.ofComponents (graphColimitIso T X Y) (fun {a b} f => by
    let τ : graphDiagram T X Y a ⟶ graphDiagram T X Y b := (graphWordDiagram T X Y).map f
    change colim.map τ ≫ (graphColimitIso T X Y b).hom =
      (graphColimitIso T X Y a).hom ≫ nerveMap
        (WordAction.functor (W := ⊤) (X := (Paths.of Q).obj X) (Y := (Paths.of Q).obj Y) f)
    apply colimit.hom_ext
    intro S
    change colimit.ι (graphDiagram T X Y a) S ≫ colim.map τ ≫
      (graphColimitIso T X Y b).hom = colimit.ι (graphDiagram T X Y a) S ≫
      (graphColimitIso T X Y a).hom ≫ nerveMap
        (WordAction.functor (W := ⊤) (X := (Paths.of Q).obj X) (Y := (Paths.of Q).obj Y) f)
    rw [← Category.assoc, colimit.ι_map, Category.assoc, graphColimitIso_fac,
      ← Category.assoc, graphColimitIso_fac]
    change nerveMap (wordActionFunctor T X Y S f ⋙ projectionFunctor T X Y b S) =
      nerveMap (projectionFunctor T X Y a S ⋙ WordAction.functor f)
    exact congrArg nerveMap (projectionFunctor_wordAction T X Y S f).symm)

lemma wordDiagram_eq (S : Finset Q) :
    (graphWordDiagram T X Y).flip.obj S =
      letI := FiniteQuiver.quiver (hull T X Y S)
      Hammock.graphDiagram (⊤ : MorphismProperty (Paths (FiniteQuiver.Vertex (hull T X Y S))))
        (left T X Y S) (right T X Y S) := by
  let := FiniteQuiver.quiver (hull T X Y S)
  rfl

end SerrePositivity.EInfinity.Hammock.RootedFinite
