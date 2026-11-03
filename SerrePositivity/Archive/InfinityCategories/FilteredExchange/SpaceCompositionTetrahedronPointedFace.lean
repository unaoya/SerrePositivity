module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionTetrahedron
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyFaces

/-!
概要：比較三単体の全 Hom 族を元の三角形の全 Hom 族へ戻す。
方針：初点を保つ面の厳密な制限と元の面の等式を使う。
規約：係数全体を固定し、各点の同型の選択へ弱めない。
使われ方：元の全族の比較と厳密合成側の比較を同じ三単体へ束ねる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ全 Hom 係数において第一面は元の三角形の実 pointed 族そのもの。 -/
lemma spaceCompositionTetrahedron_pointed_face_one (s : SpaceInfinity.{u} _⦋2⦌) :
    (stdSimplex.δ (1 : Fin 4) ▷ spaceSimplexPointedCoefficients s) ≫
      spaceSimplexPointedFamily (coherentCompositionTetrahedron s) =
        spaceSimplexPointedFamily s := by
  have hf : ∀ {r t : SpaceInfinity.{u} _⦋2⦌}, r = t →
      HEq (spaceSimplexPointedFamily r) (spaceSimplexPointedFamily t) := by
    intro r t h
    cases h
    rfl
  exact (spaceSimplexPointedFamily_positive_face
    (coherentCompositionTetrahedron s) (0 : Fin 3)).trans
      (eq_of_heq (hf (coherentCompositionTetrahedron_face_one s)))

end SerrePositivity.InfinityCategories.F2
