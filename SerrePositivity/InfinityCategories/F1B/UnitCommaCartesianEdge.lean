module

public import SerrePositivity.InfinityCategories.F1B.UnitCommaFamilies
public import SerrePositivity.InfinityCategories.Stable.FinalHornRestrictionLifting
public import SerrePositivity.InfinityCategories.Core.FunctorTerminal
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianEdge

/-!
概要：comma の標的で可逆な辺は始域射影に対して cartesian。
方針：標的の最後のホーンを埋め、区間の境界を固定して矢印の図式を相対充填する。
規約：straightening は使わず、指定された始域の単体を厳密に保つ。
使われ方：B1 の comma の始域射影の輸送を認証する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：comma の標的で可逆な辺は始域射影に対して cartesian。
方針：Y のホーンの充填と、X の区間境界の相対充填を引き戻しで組み合わせる。
規約：G の忠実性や fibration 性は要求しない。
使われ方：標的を固定した辺による comma の始域方向の輸送。 -/
lemma isCartesianEdge_unitCommaSource_of_target {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X)
    {v w : (unitComma G) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (unitComma G)) v w)
    (he : IsInvertibleEdge (e.map ((truncation 2).map (unitCommaTarget G)))) :
    IsCartesianEdge (unitCommaSource G) e.edge := by
  intro m σ β hσ sq
  obtain ⟨y, hy⟩ := hasFinalHornFillers_of_isInvertibleEdge
    (e.map ((truncation 2).map (unitCommaTarget G))) he m (σ ≫ unitCommaTarget G)
    (by change (unitCommaTarget G).app _ (σ.app _ (finalHornEdge m)) = _; rw [hσ]; rfl)
  let D := curry (intervalBoundaryDiagram β (y ≫ G))
  let a := internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (boundary 1 : SSet.{u}) X D
  let b := internalHomFlipHomEquiv
    (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) (Δ[1] : SSet.{u}) X
    (σ ≫ unitCommaArrow G)
  have hD : (horn (m + 2) (Fin.last (m + 2))).ι ≫ D =
      (σ ≫ unitCommaArrow G) ≫ (pre (boundary 1).ι).app X := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, intervalBoundaryDiagram_naturality,
      uncurry_pre_app]
    change intervalBoundaryDiagram _ _ =
      (boundary 1).ι ▷ _ ≫ unitCommaUncurry σ
    rw [unitCommaUncurry_boundary, ← sq.w, ← Category.assoc, hy]
  have hw : a ≫ (pre (horn (m + 2) (Fin.last (m + 2))).ι).app X = (boundary 1).ι ≫ b := by
    have h := congrArg (internalHomFlipHomEquiv
      (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) (boundary 1 : SSet.{u}) X) hD
    rw [internalHomFlipHomEquiv_pre, internalHomFlipHomEquiv_pre_app] at h
    exact h
  have ht (n : ℕ) (s : (Δ[1] : SSet.{u}) _⦋n⦌)
      (hs : s ∉ Set.range ((boundary 1).ι.app (Opposite.op ⦋n⦌))) :
      IsInvertibleEdge (edgeOfSimplex ((uncurry b).app (Opposite.op ⦋1⦌)
        (finalHornEdge m, PinchedHom.constant (simplexLastVertex s) 1))) := by
    have hs' : s ∉ (boundary 1).obj (Opposite.op ⦋n⦌) :=
      fun h ↦ hs ⟨⟨s, h⟩, rfl⟩
    have hv := simplexLastVertex_stdSimplex_of_notMem_boundary s hs'
    have hedge : (uncurry b).app (Opposite.op ⦋1⦌)
        (finalHornEdge m, PinchedHom.constant (simplexLastVertex s) 1) =
        G.app (Opposite.op ⦋1⦌)
          ((unitCommaTarget G).app (Opposite.op ⦋1⦌) e.edge) := by
      rw [hv]
      change (unitCommaUncurry σ).app (Opposite.op ⦋1⦌)
        (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (Fin.last 1)) 1, finalHornEdge m) = _
      have h := ConcreteCategory.congr_hom
        (NatTrans.congr_app (unitCommaUncurry_one σ) (Opposite.op ⦋1⦌)) (finalHornEdge m)
      change (unitCommaUncurry σ).app (Opposite.op ⦋1⦌)
        (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (Fin.last 1)) 1,
          finalHornEdge m) =
        G.app (Opposite.op ⦋1⦌)
          ((unitCommaTarget G).app (Opposite.op ⦋1⦌)
            (σ.app (Opposite.op ⦋1⦌) (finalHornEdge m))) at h
      rw [h, hσ]
    rw [hedge]
    exact (isInvertibleEdge_congr
      (e := edgeOfSimplex (G.app (Opposite.op ⦋1⦌)
        ((unitCommaTarget G).app (Opposite.op ⦋1⦌) e.edge)))
      (f := (e.map ((truncation 2).map (unitCommaTarget G))).map ((truncation 2).map G))
      rfl).2 (he.map G)
  obtain ⟨L, hL₀, hL₁⟩ := finalHornRestriction_lift_of_last_vertices (boundary 1).ι m a b hw ht
  let l := (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (Δ[1] : SSet.{u}) X).symm L
  have hl : internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (Δ[1] : SSet.{u}) X l = L :=
    (internalHomFlipHomEquiv _ _ _).apply_symm_apply L
  have hl₀ : l ≫ (pre (boundary 1).ι).app X = D := by
    apply (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) (boundary 1 : SSet.{u}) X).injective
    rw [internalHomFlipHomEquiv_pre_app, hl]
    exact hL₀
  have hl₁ : (horn (m + 2) (Fin.last (m + 2))).ι ≫ l = σ ≫ unitCommaArrow G := by
    apply (internalHomFlipHomEquiv
      (horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) (Δ[1] : SSet.{u}) X).injective
    rw [internalHomFlipHomEquiv_pre, hl]
    exact hL₁
  have hp : l ≫ (pre (boundary 1).ι).app X = lift β y ≫ unitCommaBoundary G := by
    rw [hl₀]
    apply uncurry_injective
    simp only [D, unitCommaBoundary, uncurry_curry, uncurry_natural_left,
      intervalBoundaryDiagram_naturality, lift_fst]
    rw [← Category.assoc, lift_snd]
  let f : (Δ[m + 2] : SSet.{u}) ⟶ unitComma G := pullback.lift l (lift β y) hp
  refine CommSq.HasLift.mk' { l := f, fac_left := ?_, fac_right := ?_ }
  · apply pullback.hom_ext
    · change _ ≫ f ≫ unitCommaArrow G = σ ≫ unitCommaArrow G
      rw [show f ≫ unitCommaArrow G = l from pullback.lift_fst _ _ _]
      exact hl₁
    · apply CartesianMonoidalCategory.hom_ext
      · change _ ≫ f ≫ unitCommaSource G = σ ≫ unitCommaSource G
        simp only [f, unitCommaSource, unitCommaPair,
          pullback.lift_snd_assoc, lift_fst]
        exact sq.w.symm
      · change _ ≫ f ≫ unitCommaTarget G = σ ≫ unitCommaTarget G
        simp only [f, unitCommaTarget, unitCommaPair,
          pullback.lift_snd_assoc, lift_snd]
        exact hy
  · change f ≫ (pullback.snd _ _ ≫ fst X Y) = β
    simp only [f, pullback.lift_snd_assoc, lift_fst]

end SerrePositivity.InfinityCategories
