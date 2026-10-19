module

public import SerrePositivity.InfinityCategories.F1B.KanUnitCommaFiberInnerFibration
public import SerrePositivity.InfinityCategories.F1B.FunctorRelativeInitial

/-!
概要：固定始域の comma の標的射影は二次元以上の先頭ホーンを持ち上げる。
方針：区間の両端を固定し、始点での恒等辺の可逆性による相対ホーン充填を使う。
規約：矢印の値域 X の quasicategory 性だけを使う。
使われ方：局所添字の区間模型の left fibration 性の外側ホーン部分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：固定始域の comma の標的射影は全ての高次の先頭ホーンを持ち上げる。
方針：境界を持つ区間の図式を二変数の交換で相対的な先頭ホーンの問題に直す。
規約：Y と G の充填性は不要、m は二次元からの差。
使われ方：left fibration の構造の外側ホーンの条件。 -/
lemma kanUnitCommaFiberProjection_hasLiftingProperty_initialHorn
    {X Y : SSet.{u}} [Quasicategory X] (G : Y ⟶ X) (x : X _⦋0⦌) (m : ℕ) :
    HasLiftingProperty (horn (m + 2) 0).ι (kanUnitCommaFiberProjection G x) := by
  constructor
  intro σ β sq
  let σ' := σ ≫ vertexFiberι (unitCommaSource G) x
  have hsource : σ' ≫ unitCommaSource G = SSet.const x := by
    dsimp only [σ']
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]
  have htarget : σ' ≫ unitCommaTarget G = (horn (m + 2) 0).ι ≫ β := sq.w
  let D := curry (intervalBoundaryDiagram (SSet.const x) (β ≫ G))
  let a := internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (boundary 1 : SSet.{u}) X D
  let b := internalHomFlipHomEquiv (horn (m + 2) 0 : SSet.{u}) (Δ[1] : SSet.{u}) X
    (σ' ≫ unitCommaArrow G)
  have hD : (horn (m + 2) 0).ι ≫ D =
      (σ' ≫ unitCommaArrow G) ≫ (pre (boundary 1).ι).app X := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, intervalBoundaryDiagram_naturality,
      uncurry_pre_app]
    change intervalBoundaryDiagram _ _ = (boundary 1).ι ▷ _ ≫ unitCommaUncurry σ'
    rw [unitCommaUncurry_boundary, hsource, htarget, SSet.comp_const, Category.assoc]
  have hw : a ≫ (pre (horn (m + 2) 0).ι).app X = (boundary 1).ι ≫ b := by
    have h := congrArg (internalHomFlipHomEquiv
      (horn (m + 2) 0 : SSet.{u}) (boundary 1 : SSet.{u}) X) hD
    rw [internalHomFlipHomEquiv_pre, internalHomFlipHomEquiv_pre_app] at h
    exact h
  have ht (n : ℕ) (s : (Δ[1] : SSet.{u}) _⦋n⦌)
      (hs : s ∉ Set.range ((boundary 1).ι.app (Opposite.op ⦋n⦌))) :
      IsInvertibleEdge (edgeOfSimplex ((uncurry b).app (Opposite.op ⦋1⦌)
        (initialHornEdge m, PinchedHom.constant (simplexFirstVertex s) 1))) := by
    have hs' : s ∉ (boundary 1).obj (Opposite.op ⦋n⦌) := fun h ↦ hs ⟨⟨s, h⟩, rfl⟩
    rw [simplexFirstVertex_stdSimplex_of_notMem_boundary s hs']
    have hedge : (uncurry b).app (Opposite.op ⦋1⦌)
        (initialHornEdge m, PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) 1) =
        PinchedHom.constant x 1 := by
      dsimp [b, internalHomFlipHomEquiv]
      rw [uncurry_curry]
      change (unitCommaUncurry σ').app (Opposite.op ⦋1⦌)
        (PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) 1, initialHornEdge m) = _
      have h := ConcreteCategory.congr_hom
        (NatTrans.congr_app (unitCommaUncurry_zero σ') (Opposite.op ⦋1⦌)) (initialHornEdge m)
      rw [hsource] at h
      exact h
    rw [hedge]
    have hi := isEquivalencePathVertex_const x
    unfold IsEquivalencePathVertex at hi
    rw [intervalFunctorVertexEdge_functorVertex] at hi
    exact hi
  obtain ⟨L, hL₀, hL₁⟩ := initialHornRestriction_lift_of_first_vertices (boundary 1).ι m a b hw ht
  let l := (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (Δ[1] : SSet.{u}) X).symm L
  have hl : internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (Δ[1] : SSet.{u}) X l = L :=
    (internalHomFlipHomEquiv _ _ _).apply_symm_apply L
  have hl₀ : l ≫ (pre (boundary 1).ι).app X = D := by
    apply (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (boundary 1 : SSet.{u}) X).injective
    rw [internalHomFlipHomEquiv_pre_app, hl]
    exact hL₀
  have hl₁ : (horn (m + 2) 0).ι ≫ l = σ' ≫ unitCommaArrow G := by
    apply (internalHomFlipHomEquiv
      (horn (m + 2) 0 : SSet.{u}) (Δ[1] : SSet.{u}) X).injective
    rw [internalHomFlipHomEquiv_pre, hl]
    exact hL₁
  have hp : l ≫ (pre (boundary 1).ι).app X = lift (SSet.const x) β ≫ unitCommaBoundary G := by
    rw [hl₀]
    apply uncurry_injective
    simp only [D, unitCommaBoundary, uncurry_curry, uncurry_natural_left,
      intervalBoundaryDiagram_naturality, lift_fst]
    rw [← Category.assoc, lift_snd]
  let f : (Δ[m + 2] : SSet.{u}) ⟶ unitComma G := pullback.lift l (lift (SSet.const x) β) hp
  have hfSource : f ≫ unitCommaSource G = SSet.const x := by
    simp only [f, unitCommaSource, unitCommaPair, pullback.lift_snd_assoc, lift_fst]
  have hfTarget : f ≫ unitCommaTarget G = β := by
    simp only [f, unitCommaTarget, unitCommaPair, pullback.lift_snd_assoc, lift_snd]
  refine CommSq.HasLift.mk' {
    l := vertexFiberLift (unitCommaSource G) x f hfSource
    fac_left := ?_
    fac_right := ?_ }
  · apply vertexFiber_hom_ext (unitCommaSource G) x
    rw [Category.assoc, vertexFiberLift_ι]
    apply pullback.hom_ext
    · change _ ≫ f ≫ unitCommaArrow G = σ' ≫ unitCommaArrow G
      rw [show f ≫ unitCommaArrow G = l from pullback.lift_fst _ _ _]
      exact hl₁
    · apply CartesianMonoidalCategory.hom_ext
      · change _ ≫ f ≫ unitCommaSource G = σ' ≫ unitCommaSource G
        rw [hfSource, SSet.comp_const, hsource]
      · change _ ≫ f ≫ unitCommaTarget G = σ' ≫ unitCommaTarget G
        rw [hfTarget, htarget]
  · change _ ≫ (vertexFiberι (unitCommaSource G) x ≫ unitCommaTarget G) = β
    rw [← Category.assoc, vertexFiberLift_ι]
    exact hfTarget

end SerrePositivity.InfinityCategories.F1B
