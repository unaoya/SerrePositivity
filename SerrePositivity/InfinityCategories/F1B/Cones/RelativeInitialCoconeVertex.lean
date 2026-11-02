module

public import SerrePositivity.InfinityCategories.F1B.Cones.CoconeShapeHomRestriction
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorPointIso
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeInitialComparison

/-!
概要：余錐形状の全関手の相対始対象性から、その元の右端の相対始対象性を回収する。
方針：定値終点への写像空間を右端へ制限し、一点の関手空間の実同型で戻す。
規約：指定全余錐と右端を保つ。射自身に fibration 性を課さない。
使われ方：点ごとの普遍余錐族の余極限から最終頂点の普遍性へ進む。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 全余錐の関手頂点の相対始対象性は、同じ元の右端の相対始対象性を含意する。 -/
lemma relativeInitial_cocone_vertex {I X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y) {p : I ⟶ X}
    (c : JoinCocone p)
    (hc : KanRelativeInitialVertex ((ihom (join I (Δ[0] : SSet.{u}))).map U)
      (functorVertex c.val)) : KanRelativeInitialVertex U c.vertex := by
  let i := joinInr I (Δ[0] : SSet.{u})
  let r := stdSimplex.isTerminalObj₀.from (join I Δ[0])
  have hp : KanRelativeInitialVertex ((ihom (Δ[0] : SSet.{u})).map U)
      (functorVertex (i ≫ c.val)) := by
    intro y
    obtain ⟨G, rfl⟩ := (functorVertexEquiv (Δ[0] : SSet.{u}) X).surjective y
    have hx := coconeShapeRight_pinchedHomMap_equivalence I c.val G
    have hy := coconeShapeRight_pinchedHomMap_equivalence I (c.val ≫ U) (G ≫ U)
    have hh := (hc (functorVertex (r ≫ G))).comp hy
    change IsSimplicialHomotopyEquivalence
      (pinchedHomMap ((ihom (join I (Δ[0] : SSet.{u}))).map U)
        (functorVertex c.val) (functorVertex (r ≫ G)) ≫
        pinchedHomMap ((pre i).app Y)
          (((ihom (join I (Δ[0] : SSet.{u}))).map U).app (Opposite.op ⦋0⦌)
            (functorVertex c.val))
          (((ihom (join I (Δ[0] : SSet.{u}))).map U).app (Opposite.op ⦋0⦌)
            (functorVertex (r ≫ G)))) at hh
    rw [← pinchedHomMap_comp] at hh
    have he := congrArg (fun k : (ihom (join I (Δ[0] : SSet.{u}))).obj X ⟶
        (ihom (Δ[0] : SSet.{u})).obj Y ↦ IsSimplicialHomotopyEquivalence
          (pinchedHomMap k (functorVertex c.val) (functorVertex (r ≫ G))))
      ((pre i).naturality U)
    have hh' := he.mp hh
    rw [pinchedHomMap_comp] at hh'
    have ht := hx.cancel_left hh'
    change IsSimplicialHomotopyEquivalence (pinchedHomMap ((ihom Δ[0]).map U)
      (functorVertex (i ≫ c.val)) (functorVertex (i ≫ (r ≫ G)))) at ht
    have he : i ≫ (r ≫ G) = G := by
      rw [← Category.assoc, stdSimplex.isTerminalObj₀.hom_ext (i ≫ r) (𝟙 _),
        Category.id_comp]
    rw [he] at ht
    exact ht
  let eX := functorPointIso X
  let eY := functorPointIso Y
  have he : eX.hom ≫ U = (ihom (Δ[0] : SSet.{u})).map U ≫ eY.hom := by rfl
  have hs : Function.Surjective (eX.hom.app (Opposite.op ⦋0⦌)) := by
    intro y
    refine ⟨eX.inv.app (Opposite.op ⦋0⦌) y, ?_⟩
    exact ConcreteCategory.congr_hom (NatTrans.congr_app eX.inv_hom_id _) y
  have h := (kanRelativeInitialVertex_iff_of_comparison
    ((ihom (Δ[0] : SSet.{u})).map U) U eX.hom eY.hom he
    (qCatEquivalenceOfIso eX).isFullyFaithful
    (qCatEquivalenceOfIso eY).isFullyFaithful hs (functorVertex (i ≫ c.val))).mp hp
  change KanRelativeInitialVertex U ((evaluateFunctorAt _).app
    (Opposite.op ⦋0⦌) (functorVertex (i ≫ c.val))) at h
  rw [evaluateFunctorAt_functorVertex] at h
  exact h

end SerrePositivity.InfinityCategories.F1B
