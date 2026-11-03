module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentHomLastPost
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentRightSlicePost

/-!
概要：元の右 Hom から実右 slice への同じ全比較は、指定終域射の後合成に厳密に自然。
方針：元の Hom 単体の座標と、同じ指定後合成の全 Hom の一致を束ねる。
規約：元の比較・fiber 包含・全パラメータを保持。使われ方：Ncomp の輸送比較の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C}
local notation "J(" A "," B ")" => coherentHomComparison A B ≫
  pinchedHomToSliceFiber (coherentNerveVertex A) (coherentNerveVertex B) ≫
    vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm (coherentNerveVertex B)))
      (coherentNerveVertex A)

/-- 元の右 Hom 比較を実右 slice で読むと、元の Hom 比較単体を厳密に回収する。 -/
lemma coherentHomSliceSimplex_coordinate {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) :
    coherentRightSliceSimplex Y ((J(X,Y)).app (Opposite.op ⦋n⦌) (ULift.up σ)) =
      coherentHomComparisonSimplex σ := by
  change SSet.yonedaEquiv ((joinStdSimplexIso n 0).inv ≫
    ((joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm (coherentHomComparisonSimplex σ))) = _
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp, Equiv.apply_symm_apply]

/-- 元の右 Hom の実全比較の各単体は、同じ指定終域射の後合成を保持する。 -/
lemma coherentHomSliceSimplex_post {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) (g : Y ⟶ Z) :
    coherentRightSlicePostSimplex g ((J(X,Y)).app (Opposite.op ⦋n⦌) (ULift.up σ)) =
      (J(X,Z)).app (Opposite.op ⦋n⦌)
        (ULift.up ((eHomWhiskerLeft SSet X g).app (Opposite.op ⦋n⦌) σ)) := by
  apply coherentRightSliceSimplex_injective Z
  rw [coherentRightSlicePostSimplex_coordinate,
    coherentHomSliceSimplex_coordinate ((eHomWhiskerLeft SSet X g).app (Opposite.op ⦋n⦌) σ)]
  have e := coherentSimplexLastPost_of_source_eq (coherentHomSliceSimplex_coordinate σ)
    (coherentRightSliceSimplex_last Y ((J(X,Y)).app (Opposite.op ⦋n⦌) (ULift.up σ)))
    (coherentHomComparisonObj_last X Y n) g
  exact e.trans (coherentHomComparisonSimplex_last_post σ g)

/-- 元の全右 Hom 比較は、実右 slice の指定後合成と全単体で厳密に可換。 -/
lemma coherentHomSliceComparison_post (g : Y ⟶ Z) :
    J(X,Y) ≫ coherentRightSlicePost g =
      (SSet.uliftFunctor.{v, u}).map (eHomWhiskerLeft SSet X g) ≫ J(X,Z) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ⟩
  exact coherentHomSliceSimplex_post σ g

end SerrePositivity.InfinityCategories.F2
