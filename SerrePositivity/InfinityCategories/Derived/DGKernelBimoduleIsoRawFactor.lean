module
public import SerrePositivity.InfinityCategories.Derived.DGKernelBimoduleIso
/-!
概要：元の双加群同型の導来作用と同じ raw factor の可換四角形を証明する。
方針：元の指定値と同じ実変形円柱を保って照合する。
規約：原 Hom の平坦性を追加しない。使われ方：K-flat 比較 ξ の自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- 元の半自由出力分解へ送った同型は、同じ raw factor と可換。 -/
lemma dgModuleResolvedInfinity_isoOfRawFunctorIso_square
    (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
    (E : Type v) [DGCategory R E] [Small.{u} E]
    (F G : DGFunctor R C (RightModule R E))
    (e : FunctorIso (dgNerve.map F) (dgNerve.map G)) :
    dgModuleResolvedInfinity_isoOfRawFunctorIso R C E F G e ≪≫
        dgModuleResolvedInfinity_rawFactorIso R C E G =
      dgModuleResolvedInfinity_rawFactorIso R C E F ≪≫
        e.postcomp (dgModuleResolvedInfinity R (RightModule R E) E
          (DGFunctor.id (RightModule R E))) := by
  simp only [dgModuleResolvedInfinity_isoOfRawFunctorIso, Iso.trans_assoc,
    Iso.symm_self_id, Iso.trans_refl]
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 元の双加群同型の通常作用を、同じ半自由入力へ制限する。 -/
def dgKernelBimoduleIsoSemifreeNerve {P Q : BimoduleCategory R E D} (e : P ≅ Q) :
    FunctorIso
      (dgNerve.map (dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P)))
      (dgNerve.map (dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D Q))) := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)
  have h := (dgKernelTensorIsoNerveOfBimoduleIso R D E e).precomp (dgNerve.map I)
  simpa only [dgSemifreeKernelModuleDG, dgNerve.map_comp] using! h
/-- 元の双加群同型の導来作用は、同じ raw factor と可換。 -/
lemma dgKernelDerivedInfinity_bimoduleIso_rawFactor_square
    {P Q : BimoduleCategory R E D} (e : P ≅ Q) :
    dgKernelDerivedInfinity_bimoduleIso R D E e ≪≫
      dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) E
        (dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D Q)) =
    dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) E
      (dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P)) ≪≫
      (dgKernelBimoduleIsoSemifreeNerve R D E e).postcomp
        (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E))) := by
  exact dgModuleResolvedInfinity_isoOfRawFunctorIso_square R (SemifreeDGModules R D) E
    (dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P))
    (dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D Q))
    (dgKernelBimoduleIsoSemifreeNerve R D E e)
end
end SerrePositivity.InfinityCategories
