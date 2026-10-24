module
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedWhiskerAlgebra
/-!
概要：元の augmentation 比較の射は、後続作用間の任意の全関手射に自然である。
方針：同じ全単体ホモトピーの後合成の射を回収し、型付き交換則を使う。
規約：後続作用の平坦性・射の可逆性を要求しない。使われ方：元の κ の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
open scoped Simplicial
lemma functorIsoOfPointwiseInvertibleHomotopy_postcomp_hom
    {A X Y : SSet.{w}} [Quasicategory Y] {f g : A ⟶ X}
    (H : SSet.Homotopy f g) (q : X ⟶ Y)
    (hq : ∀ k : A _⦋0⦌,
      IsInvertibleEdge (simplicialHomotopyVertexEdge (functorHomotopyPostcomp H q) k).toTruncated) :
    (functorIsoOfPointwiseInvertibleHomotopy (functorHomotopyPostcomp H q) hq).hom =
      functorHomPostcomp f g q
        (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) :=
  functorHomotopyPostcomp_hom H q
lemma functorHomotopyPostcomp_hom_typed {A X Y : SSet.{w}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) (q : X ⟶ Y) :
    SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp H q)) =
      functorHomPostcomp f g q
        (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) :=
  functorHomotopyPostcomp_hom H q
end SerrePositivity.InfinityCategories
