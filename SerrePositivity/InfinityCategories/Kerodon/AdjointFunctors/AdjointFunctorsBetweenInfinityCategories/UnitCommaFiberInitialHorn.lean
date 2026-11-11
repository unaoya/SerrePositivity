module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberInnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorRelativeInitial

/-!
概要：固定始域の comma の標的射影は二次元以上の先頭ホーンを持ち上げる。
方針：区間の両端を固定し、始点での恒等辺の可逆性による相対ホーン充填を使う。
規約：矢印の値域 X の quasicategory 性だけを使う。
使われ方：局所添字の区間模型の left fibration 性の外側ホーン部分。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：固定始域の comma の標的射影は全ての高次の先頭ホーンを持ち上げる。
方針：境界を持つ区間の図式を二変数の交換で相対的な先頭ホーンの問題に直す。
規約：Y と G の充填性は不要、m は二次元からの差。
使われ方：left fibration の構造の外側ホーンの条件。 -/
lemma unitCommaFiberProjection_hasLiftingProperty_initialHorn
    {X Y : SSet.{u}} [Quasicategory X] (G : Y ⟶ X) (x : X _⦋0⦌) (m : ℕ) :
    HasLiftingProperty (horn (m + 2) 0).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x) := by
  constructor
  intro σ β sq
  let σ' := σ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x
  have hsource : σ' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = SSet.const x := by
    dsimp only [σ']
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  have htarget : σ' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G = (horn (m + 2) 0).ι ≫ β := sq.w
  let D := curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (SSet.const x) (β ≫ G))
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (boundary 1 : SSet.{u}) X D
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (horn (m + 2) 0 : SSet.{u}) (Δ[1] : SSet.{u}) X
    (σ' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G)
  have hD : (horn (m + 2) 0).ι ≫ D =
      (σ' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G) ≫ (pre (boundary 1).ι).app X := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality,
      uncurry_pre_app]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram _ _ = (boundary 1).ι ▷ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry σ'
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry_boundary, hsource, htarget, SSet.comp_const, Category.assoc]
  have hw : a ≫ (pre (horn (m + 2) 0).ι).app X = (boundary 1).ι ≫ b := by
    have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv
      (horn (m + 2) 0 : SSet.{u}) (boundary 1 : SSet.{u}) X) hD
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app] at h
    exact h
  have ht (n : ℕ) (s : (Δ[1] : SSet.{u}) _⦋n⦌)
      (hs : s ∉ Set.range ((boundary 1).ι.app (Opposite.op ⦋n⦌))) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((uncurry b).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s) 1))) := by
    have hs' : s ∉ (boundary 1).obj (Opposite.op ⦋n⦌) := fun h ↦ hs ⟨⟨s, h⟩, rfl⟩
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorRelativeInitial.simplexFirstVertex_stdSimplex_of_notMem_boundary s hs']
    have hedge : (uncurry b).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) 1) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1 := by
      dsimp [b, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv]
      rw [uncurry_curry]
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry σ').app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) 1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m) = _
      have h := ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry_zero σ') (Opposite.op ⦋1⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m)
      rw [hsource] at h
      exact h
    rw [hedge]
    have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isEquivalencePathVertex_const x
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex at hi
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex] at hi
    exact hi
  obtain ⟨L, hL₀, hL₁⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornRestriction_lift_of_first_vertices (boundary 1).ι m a b hw ht
  let l := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (Δ[1] : SSet.{u}) X).symm L
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (Δ[1] : SSet.{u}) X l = L :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv _ _ _).apply_symm_apply L
  have hl₀ : l ≫ (pre (boundary 1).ι).app X = D := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (boundary 1 : SSet.{u}) X).injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app, hl]
    exact hL₀
  have hl₁ : (horn (m + 2) 0).ι ≫ l = σ' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv
      (horn (m + 2) 0 : SSet.{u}) (Δ[1] : SSet.{u}) X).injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre, hl]
    exact hL₁
  have hp : l ≫ (pre (boundary 1).ι).app X = lift (SSet.const x) β ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaBoundary G := by
    rw [hl₀]
    apply uncurry_injective
    simp only [D, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaBoundary, uncurry_curry, uncurry_natural_left,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality, lift_fst]
    rw [← Category.assoc, lift_snd]
  let f : (Δ[m + 2] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G := pullback.lift l (lift (SSet.const x) β) hp
  have hfSource : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = SSet.const x := by
    simp only [f, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaPair, pullback.lift_snd_assoc, lift_fst]
  have hfTarget : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G = β := by
    simp only [f, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaPair, pullback.lift_snd_assoc, lift_snd]
  refine CommSq.HasLift.mk' {
    l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x f hfSource
    fac_left := ?_
    fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    apply pullback.hom_ext
    · change _ ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G = σ' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G
      rw [show f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G = l from pullback.lift_fst _ _ _]
      exact hl₁
    · apply CartesianMonoidalCategory.hom_ext
      · change _ ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = σ' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G
        rw [hfSource, SSet.comp_const, hsource]
      · change _ ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G = σ' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G
        rw [hfTarget, htarget]
  · change _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G) = β
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    exact hfTarget

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
