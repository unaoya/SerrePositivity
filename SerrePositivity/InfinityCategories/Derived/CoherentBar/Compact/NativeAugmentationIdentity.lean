module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeCoconeFamily
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeUniversalMapUnique
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftHomComparison
/-!
概要：正規化 bar 自身の余錐から回収した閉増大は恒等射である。
方針：零パラメーターの全 Hom 成分を既存の余錐族の単位計算へ比較する。
規約：元の coherent 図式と全次数成分を保持し、終点の等号は異種等号で運ぶ。
使われ方：同じ native 余錐を評価したホモロジーの余極限性の照合。
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

lemma dgBarCompactCoconeCandidate_family
    (y : (dgNerve R (RightModule R D)) _⦋0⦌)
    (c : (coconeMappingSpace F y) _⦋0⦌) :
    HEq (dgCoherentBarCoconeHomCandidate R D F hMC c.val)
      (dgCoherentBarCoconeFamilyHom R D F hMC y c) := by
  apply dgCoherentBarNativeHom_heq_of_columns R D F hMC
  · change dgNerve.vertexEquiv R (RightModule R D) ((sliceUnderProjection F).app _ c.val) = _
    rw [c.property, InfinityCategories.PinchedHom.constant_zero]
  · norm_num
  · intro s
    have hL := dgCoherentBarCoconeHomCandidate_nondegenerate R D F hMC c.val s
    have hR := dgCoherentBarCoconeFamilyHom_nondegenerate R D F hMC y c s
    apply (heq_of_eq hL).trans
    apply HEq.trans ?_ (heq_of_eq hR).symm
    unfold dgCoherentBarCoconeNativeCoefficients dgCoherentBarCoconeColumn
      dgCoherentBarCoconeFamilyColumn
    apply (gradedHomTransport_heq _ _ _ _).trans
    apply (gradedHomTransport_heq _ _ _ _).trans
    apply HEq.trans ?_ (gradedHomTransport_heq _ _ _ _).symm
    exact SimplexData.hom_heq_of_indices_degree
      (dgCoherentBarCoconeSimplex R D F c.val s.val.2).toSimplexData
      rfl rfl rfl (by omega)

lemma dgBarCompactNativeAugmentation_cycle_identity :
    HEq (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgCoherentBarCoconeUniversalMap R D F hMC
        (dgCoherentBarNormalizedNativeCocone R D F hMC)))).val
      (unitElement R (dgCoherentBarNormalizedModule R D F hMC)).val := by
  rw [dgCoherentBarCoconeUniversalMap_cycle]
  exact (dgBarCompactCoconeCandidate_family R D F hMC
    (dgCoherentBarNativeApex R D F hMC) (dgCoherentBarNativeCoconePoint R D F hMC)).trans
      (dgCoherentBarNativeCoconePoint_hom R D F hMC)

private lemma dgBarCompact_isIso_of_cycle_identity {M N : RightModule R D}
    (f : ForgetEnrichment.of (Complex R) M ⟶ ForgetEnrichment.of (Complex R) N)
    (hN : N = M)
    (hf : HEq (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val
      (unitElement R M).val) : IsIso f := by
  subst N
  have he : f = 𝟙 _ := by
    apply (closedHomEquiv R (RightModule R D) _ _).injective
    apply Subtype.ext
    change (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val = _
    exact eq_of_heq hf
  rw [he]
  infer_instance

lemma dgBarCompactNativeAugmentation_isIso :
    IsIso (dgCoherentBarCoconeUniversalMap R D F hMC
      (dgCoherentBarNormalizedNativeCocone R D F hMC)) := by
  apply dgBarCompact_isIso_of_cycle_identity R D
  · unfold dgCoherentBarCoconeModule
    rw [dgCoherentBarNormalizedNativeCocone_vertex]
    rfl
  · exact dgBarCompactNativeAugmentation_cycle_identity R D F hMC

end SerrePositivity.InfinityCategories
