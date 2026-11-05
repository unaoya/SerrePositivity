module

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteDenominatorRefinement
public import SerrePositivity.KST.LocalizingInvariants.CorePreimageComparisonPrism
public import SerrePositivity.InfinityCategories.Derived.DGRoofSliceVertices
public import SerrePositivity.InfinityCategories.Derived.FiniteConeOpposite
public import SerrePositivity.InfinityCategories.HomotopyLimits.IteratedSliceOverFamilies
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalFilteredPoset

/-!
概要：固定終点への実 Verdier 分母の全 slice 部分圏は余 filtered。
方針：有限拡大図式の実共通精密化を、元の実 slice の全錐へ戻す。
規約：通常の分母圏の nerve や有限頂点族へ置き換えない。
使われ方：実分数族の有限同時精密化の添字 ∞ 圏。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- 固定した元の終点へ入る実分母の、実 slice 内の全部分複体。 -/
def verdierDenominatorOver {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B)
    (x : B.obj _⦋0⦌) : (sliceOver (SSet.yonedaEquiv.symm x)).Subcomplex :=
  fullSubcomplexOnVertices _ (fun v =>
    (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm x) v).edge ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i)

instance verdierDenominatorOver_quasicategory {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x : B.obj _⦋0⦌) :
    Quasicategory (verdierDenominatorOver i x : SSet.{u}) := by
  dsimp only [verdierDenominatorOver]
  infer_instance

/-- 任意の有限な実分母図式は、同じ実 slice 部分圏の中で全錐を持つ。 -/
lemma exists_verdierDenominatorOver_finiteCone
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)
    {K : SSet.{u}} [K.Finite] (D : K ⟶ (verdierDenominatorOver i x : SSet.{u})) :
    Nonempty (JoinCone D) := by
  let f := D ≫ (verdierDenominatorOver i x).ι
  let t : JoinCocone (f ≫ sliceOverProjection (SSet.yonedaEquiv.symm x)) :=
    ⟨sliceOverUncurry f, sliceOverUncurry_projection f⟩
  have ht : ∀ a : K _⦋0⦌,
      (t.leg (SSet.yonedaEquiv.symm a)).edge ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i := by
    intro a
    have ha := fullSubcomplexOnVertices_vertex (D.app (Opposite.op ⦋0⦌) a)
    have hy : SSet.yonedaEquiv.symm a ≫ f =
        SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) a) := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      joinMap (SSet.yonedaEquiv.symm a) (𝟙 Δ[0]) ≫ sliceOverUncurry f) ∈ _
    rw [← sliceOverUncurry_precomp, hy, sliceOverUncurry_yoneda]
    exact ha
  obtain ⟨c, _, hc, _⟩ := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierFiniteDenominatorRefinement h t ht
  let L := (joinAssociator (Δ[0] : SSet.{u}) K (Δ[0] : SSet.{u})).hom ≫ c.val
  have hL : joinInr (join (Δ[0] : SSet.{u}) K) Δ[0] ≫ L =
      SSet.yonedaEquiv.symm x := by
    dsimp only [L]
    rw [← Category.assoc, joinAssociator_last, Category.assoc,
      c.property, sliceOverUncurry_fixed]
  let G := sliceOverCurry L hL
  have hG : joinInr (Δ[0] : SSet.{u}) K ≫ G = f := by
    apply sliceOverUncurry_injective (SSet.yonedaEquiv.symm x)
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry]
    change joinMap (joinInr Δ[0] K) (𝟙 Δ[0]) ≫
      ((joinAssociator Δ[0] K Δ[0]).hom ≫ c.val) = sliceOverUncurry f
    rw [← Category.assoc, joinAssociator_rightPair, c.property]
  have hLv : InvertsEdges (L ≫ q.hom) Set.univ := by
    dsimp only [L]
    rw [Category.assoc]
    exact invertsAllEdges_precomp _ _ hc
  have hv : ∀ v : (join (Δ[0] : SSet.{u}) K) _⦋0⦌,
      (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm x)
        (G.app (Opposite.op ⦋0⦌) v)).edge ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i := by
    intro v
    let u : (Δ[1] : SSet.{u}) ⟶ join (join (Δ[0] : SSet.{u}) K) Δ[0] :=
      (joinStdSimplexIso 0 0).inv ≫ joinMap (SSet.yonedaEquiv.symm v) (𝟙 Δ[0])
    have hy : SSet.yonedaEquiv.symm v ≫ G =
        SSet.yonedaEquiv.symm (G.app (Opposite.op ⦋0⦌) v) := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have he : (G.app (Opposite.op ⦋0⦌) v).val =
        joinMap (SSet.yonedaEquiv.symm v) (𝟙 Δ[0]) ≫ L := by
      rw [← sliceOverUncurry_yoneda, ← hy, sliceOverUncurry_precomp,
        sliceOverUncurry_curry]
    apply (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.mem_weakEquivalences_iff_invertible h
      (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm x) (G.app _ v))).mpr
    apply (isInvertibleEdge_congr (e :=
      (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm x) (G.app _ v)).map
        ((truncation 2).map q.hom)) (f :=
          (edgeOfSimplex (SSet.yonedaEquiv u)).map ((truncation 2).map (L ≫ q.hom))) ?_).mpr
    · exact hLv (a := SSet.yonedaEquiv u) (Set.mem_univ _)
    · change q.hom.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ (G.app _ v).val)) =
          q.hom.app (Opposite.op ⦋1⦌) (L.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv u))
      rw [he, ← SSet.yonedaEquiv_comp]
      rfl
  let R : join (Δ[0] : SSet.{u}) K ⟶ (verdierDenominatorOver i x : SSet.{u}) :=
    fullSubcomplexLift (fun v =>
    (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm x) v).edge ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) G hv
  have hRi : R ≫ (verdierDenominatorOver i x).ι = G := fullSubcomplexLift_ι _ _ _
  refine ⟨⟨R, ?_⟩⟩
  apply (cancel_mono (verdierDenominatorOver i x).ι).mp
  rw [Category.assoc, hRi]
  exact hG

/-- 実分母 over の反対 ∞ 圏は、全有限単体集合を試験する filtered ∞ 圏。 -/
lemma verdierDenominatorOver_op_isFilteredInfinity
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌) :
    F2.IsFilteredInfinity (verdierDenominatorOver i x : SSet.{u}).op :=
  isFilteredInfinity_op_of_finiteCones _ (exists_verdierDenominatorOver_finiteCone h x)

/-- 実分母添字には、小さい通常の filtered poset からの実 cofinal 表示がある。 -/
lemma exists_verdierDenominatorOver_cofinal_filteredPoset
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌) :
    ∃ (I : Type u) (o : PartialOrder I),
      letI := o
      ∃ f : nerve I ⟶ (verdierDenominatorOver i x : SSet.{u}).op,
        IsCardinalFiltered.{u, u, u} I Cardinal.aleph0 ∧ IsRightCofinal f := by
  have : F2.IsFilteredInfinity (verdierDenominatorOver i x : SSet.{u}).op :=
    verdierDenominatorOver_op_isFilteredInfinity h x
  have : F2.IsKappaFiltered Cardinal.aleph0 (verdierDenominatorOver i x : SSet.{u}).op :=
    (F2.isKappaFiltered_aleph0_iff _).mpr inferInstance
  exact F2.Ind.exists_cofinal_cardinalFiltered_poset (κ := Cardinal.aleph0)
    (verdierDenominatorOver i x : SSet.{u}).op

end SerrePositivity.KST.LocalizingInvariants
