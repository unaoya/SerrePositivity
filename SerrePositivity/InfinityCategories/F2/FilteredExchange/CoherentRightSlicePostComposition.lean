module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentRightSlicePost
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentSimplexLastPostComposition

/-!
概要：元の coherent 右 slice の指定後合成写像は、元の二射の合成を厳密に保つ。
方針：同じ全錐の豊穣座標で、最後の後合成の厳密合成則を使う。
規約：同型や各頂点の比較へ弱めない。使われ方：元の二射と合成 prism の高次整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {Z W V : C}
  (g : Z ⟶ W) (h : W ⟶ V)

/-- 元の二射の右 slice 後合成は、元の合成射の後合成と全単体で厳密に一致する。 -/
lemma coherentRightSlicePost_comp :
    coherentRightSlicePost g ≫ coherentRightSlicePost h = coherentRightSlicePost (g ≫ h) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro c
  apply coherentRightSliceSimplex_injective V
  change coherentRightSliceSimplex V
    (coherentRightSlicePostSimplex h (coherentRightSlicePostSimplex g c)) =
    coherentRightSliceSimplex V (coherentRightSlicePostSimplex (g ≫ h) c)
  rw [coherentRightSlicePostSimplex_coordinate h, coherentRightSlicePostSimplex_coordinate (g ≫ h)]
  have e := coherentSimplexLastPost_of_source_eq (coherentRightSlicePostSimplex_coordinate g c)
    (coherentRightSliceSimplex_last W (coherentRightSlicePostSimplex g c))
    (coherentSimplexLastPost_last (coherentRightSliceSimplex Z c)
      (eqToHom (coherentRightSliceSimplex_last Z c) ≫ g)) h
  refine e.trans ((coherentSimplexLastPost_comp (coherentRightSliceSimplex Z c)
    (eqToHom (coherentRightSliceSimplex_last Z c) ≫ g) h).trans ?_)
  rw [Category.assoc]

end SerrePositivity.InfinityCategories.F2
