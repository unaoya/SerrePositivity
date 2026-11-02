module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfTriangulated
public import SerrePositivity.InfinityCategories.Derived.DGModuleExtensionYonedaStrict
public import SerrePositivity.InfinityCategories.Derived.DGModuleStrictNatTransIso
/-!
概要：任意の加群値 dg 関手を Yoneda 後の同じ kernel tensor と実関手同型で比較する。
方針：既存の tensor・Yoneda の厳密同定と対角右単位の全 Hom 自然性を使う。
規約：Small 仮定は二つの係数 dg 圏だけに置く。
使われ方：前三角始域から全加群圏への任意の dg 関手の完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D C : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R C] [Small.{u} C]
  (P : Bimodule R C D)

lemma dgKernelTensorYoneda_naturality (d d' : D) :
    ((dgYoneda R D).comp (Morita.kernelTensor R D C P)).map d d' ≫
      moduleHomPostcompose R C _ _ _ (BimoduleTensor.rightUnitIso R C D P d').hom =
    P.toFunctor.map d d' ≫
      moduleHomPrecompose R C _ _ _ (BimoduleTensor.rightUnitIso R C D P d).hom := by
  have hh : ∀ (F G : DGFunctor R D (RightModule R C)), F = G →
      HEq (F.map d d') (G.map d d') := by
    intro F G h
    cases h
    rfl
  have hm0 := hh ((dgYoneda R D).comp (Morita.kernelTensor R D C P))
    (BimoduleTensor.compose R C D D P (Bimodule.diagonal R D)).toFunctor
    (Morita.criterionPerfYonedaTensor_eq R D C P)
  have hm := eq_of_heq hm0
  rw [hm]
  exact BimoduleTensor.rightUnitIso_naturality R C D P d d'

def dgKernelTensorYonedaStrict :
    StrictNatTrans ((dgYoneda R D).comp (Morita.kernelTensor R D C P)) P.toFunctor :=
  dgModuleStrictNatTransOfHomNaturality R C
    (fun d => (BimoduleTensor.rightUnitIso R C D P d).hom)
    (dgKernelTensorYoneda_naturality R D C P)

def dgKernelTensorYonedaCompositeIso :
    FunctorIso
      (dgNerve.map ((dgUniverseLiftDown.{u, v, max (u + 1) v} R D).comp (dgYoneda R D)) ≫
        dgNerve.map (Morita.kernelTensor R D C P))
      (dgNerve.map ((dgUniverseLiftDown.{u, v, max (u + 1) v} R D).comp P.toFunctor)) := by
  let L := dgUniverseLiftDown.{u, v, max (u + 1) v} R D
  have he : (L.comp (dgYoneda R D)).comp (Morita.kernelTensor R D C P) =
      L.comp ((dgYoneda R D).comp (Morita.kernelTensor R D C P)) := by
    apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
    intro x y
    simp only [EnrichedFunctor.comp_map, Category.assoc, eqToHom_refl, Category.comp_id]
  rw [← dgNerve.map_comp, he]
  exact dgModuleFunctorIsoOfStrictNatTrans R C
    (dgStrictNatTransPrecomp L (dgKernelTensorYonedaStrict R D C P))
    (fun x => (BimoduleTensor.rightUnitIso R C D P x.label.down).hom)
    (fun _ => rfl) (fun _ => inferInstance)

end SerrePositivity.InfinityCategories
