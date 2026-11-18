module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementUniversalReindex

/-!
概要：元の全単体列の普遍単体を、終端を変える全再添字で比較する。
方針：普遍族の全再添字式を同じ恒等単体で評価し、単体的自然性を使う。
規約：元の終端の frame 射を後合成として保持する。
使われ方：大域 prism の高次成分の全 reindexing。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementUniversalSimplex_reindex {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X
      ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj (Fin.last n)))).map θ.op
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalSimplex A X Y c) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Complex A) (E := Complex A) (x := X) (x' := X)
      (homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))))))).app (Opposite.op ⦋m⦌)
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalSimplex A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) := by
  have h := congrArg (fun f : SSet.uliftFunctor.{u + 1, u}.obj (Δ[m] : SSet.{u}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj (Fin.last n))) =>
      f.app (Opposite.op ⦋m⦌) (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋m⦌))))
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalFamily_reindex A X Y c θ)
  let q : (SSet.uliftFunctor.{u + 1, u}.obj (Δ[n] : SSet.{u})).obj (Opposite.op ⦋n⦌) :=
    ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))
  have hn := ConcreteCategory.congr_hom
    ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementUniversalFamily A X Y c).naturality θ.op) q
  exact hn.symm.trans h

end SerrePositivity.ComplexLimits
