module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeRecoveredSimplices
/-!
概要：余錐族の回収した実 HA 単体を、正規化 bar の一点下の実 coslice へ束ねる。
方針：join 同型で各実単体を戻し、全面・全退化の自然性で束ねる。
規約：射影を厳密に保ち、標準の全 Hom の族の比較に使う。
使われ方：固定終点ごとの標準族を恒等余錐の Hom の族へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

def dgCoherentBarCoconePointComparisonSimplex {n : ℕ} (c : (sliceUnder F) _⦋n⦌) :
    (sliceUnder ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarNativeApex R D F hMC))) _⦋n⦌ := by
  refine ⟨(joinStdSimplexIso 0 n).hom ≫
    (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarCoconeRecoveredSimplex R D F hMC c), ?_⟩
  rw [← Category.assoc, dgCoherentBarJoinLeft_inl, SSet.yonedaEquiv_symm_naturality_left]
  exact congrArg (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
    (dgCoherentBarCoconeRecoveredSimplex_left R D F hMC c)

def dgCoherentBarCoconePointComparison : sliceUnder F ⟶
    sliceUnder ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
      (dgCoherentBarNativeApex R D F hMC)) where
  app n := ↾fun c => dgCoherentBarCoconePointComparisonSimplex R D F hMC
    (n := n.unop.len) c
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    change (joinStdSimplexIso 0 m).hom ≫
      (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
        (dgCoherentBarCoconeRecoveredSimplex R D F hMC ((sliceUnder F).map α.unop.op c)) =
      joinMap (𝟙 Δ[0]) (SSet.stdSimplex.map α.unop) ≫
        ((joinStdSimplexIso 0 n).hom ≫
          (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
            (dgCoherentBarCoconeRecoveredSimplex R D F hMC c))
    have he := dgCoherentBarCoconeRecoveredSimplex_map R D F hMC c α.unop.toOrderHom
    change dgCoherentBarCoconeRecoveredSimplex R D F hMC ((sliceUnder F).map α.unop.op c) =
      (dgCoherentBarCoconeRecoveredSimplex R D F hMC c).pullback
        (dgCoherentBarJoinOrderMap (OrderHom.id : Fin 1 →o Fin 1) α.unop.toOrderHom) at he
    rw [he]
    change (joinStdSimplexIso 0 m).hom ≫
      (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
        ((dgNerve R (RightModule R D)).map (SimplexCategory.mkHom
          (dgCoherentBarJoinOrderMap (OrderHom.id : Fin 1 →o Fin 1)
            α.unop.toOrderHom)).op (dgCoherentBarCoconeRecoveredSimplex R D F hMC c)) = _
    rw [← SSet.yonedaEquiv_symm_naturality_left, ← Category.assoc]
    have hNat := dgCoherentBarJoinStdSimplex_naturality (𝟙 ⦋0⦌) α.unop
    have hId : (𝟙 ⦋0⦌) = SimplexCategory.Hom.mk (OrderHom.id : Fin 1 →o Fin 1) := by
      ext i
      rfl
    rw [hId, SSet.stdSimplex.map_id, SimplexCategory.Hom.toOrderHom_mk] at hNat
    simpa only [Category.assoc] using congrArg (fun g => g ≫
      (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
        (dgCoherentBarCoconeRecoveredSimplex R D F hMC c)) hNat.symm

lemma dgCoherentBarCoconePointComparison_projection :
    dgCoherentBarCoconePointComparison R D F hMC ≫ sliceUnderProjection
      ((SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
        (dgCoherentBarNativeApex R D F hMC)) = sliceUnderProjection F := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro c
  change SSet.yonedaEquiv (joinInr Δ[0] Δ[n] ≫
    ((joinStdSimplexIso 0 n).hom ≫
      (SSet.yonedaEquiv (X := dgNerve R (RightModule R D))).symm
        (dgCoherentBarCoconeRecoveredSimplex R D F hMC c))) = _
  rw [← Category.assoc, dgCoherentBarJoinRight_inr,
    SSet.yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply]
  exact dgCoherentBarCoconeRecoveredSimplex_right R D F hMC c

end SerrePositivity.InfinityCategories
