module

public import SerrePositivity.InfinityCategories.F2.CoherentCompositionTetrahedronStrictFace
public import SerrePositivity.InfinityCategories.F2.CoherentCompositionTetrahedronDegenerateFace
/-!
概要：合成比較の零面と退化した最後面から、最大化後の最初の辺を厳密に回収する。
方針：同じ三単体の共有面と元の退化の恒等式を使う。
規約：元の辺を保持。使われ方：零面の指定比較の実初辺を固定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
/-- 最大化した元の三角形の最初の辺は、元の最初の辺そのもの。 -/
lemma coherentCompositionMaximalization_first_edge (s : SpaceInfinity.{u} _⦋2⦌) :
    SpaceInfinity.δ 2 (coherentSimplexMaximalization s) = SpaceInfinity.δ 2 s := by
  have hz := congrArg (fun t => SpaceInfinity.δ 2 t) (coherentCompositionTetrahedron_face_zero s)
  have hfaces := ConcreteCategory.congr_hom
    (SimplicialObject.δ_comp_δ SpaceInfinity (i := (0 : Fin 3)) (j := 2) (by decide))
    (coherentCompositionTetrahedron s)
  have hdeg := ConcreteCategory.congr_hom
    (SimplicialObject.δ_comp_σ_self SpaceInfinity (i := (0 : Fin 2)))
    (SpaceInfinity.δ 2 s)
  change SpaceInfinity.δ 0 (SpaceInfinity.δ 3 (coherentCompositionTetrahedron s)) =
    SpaceInfinity.δ 2 (SpaceInfinity.δ 0 (coherentCompositionTetrahedron s)) at hfaces
  change SpaceInfinity.δ 0 (SpaceInfinity.σ 0 (SpaceInfinity.δ 2 s)) = SpaceInfinity.δ 2 s at hdeg
  exact hz.symm.trans (hfaces.symm.trans
    ((congrArg (fun t => SpaceInfinity.δ 0 t)
      (coherentCompositionTetrahedron_face_three s)).trans hdeg))
end SerrePositivity.InfinityCategories.F2
