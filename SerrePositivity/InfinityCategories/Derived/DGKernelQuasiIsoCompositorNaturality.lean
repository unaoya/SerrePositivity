module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedCompositionHomNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedComparisonCoherence
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
/-!
概要：元の κ の全射自然性を準同型比較の同型正方形へ移す。
方針：既存の同じ射の作用・比較の逆・合成則を使う。
規約：指定比較の値を保持する。使われ方：実 diagonal span の tensor 像。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R F] [Small.{u} F]
  {P P' : BimoduleCategory R E D} {Q Q' : BimoduleCategory R F E}
  (f : P ⟶ P') (g : Q ⟶ Q')
  (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
  (hP' : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P'))
  (hQ : Bimodule.rightRelativeKFlat R F E (BimoduleCategory.underlying R F E Q))
  (hQ' : Bimodule.rightRelativeKFlat R F E (BimoduleCategory.underlying R F E Q'))
  (hf : BimoduleCategory.quasiIso R E D f) (hg : BimoduleCategory.quasiIso R F E g)
include hQ hQ' in
lemma dgKernelDerivedInfinity_compIso_quasiIso_naturality :
    dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F
      (BimoduleCategory.underlying R E D P) (BimoduleCategory.underlying R F E Q) hP ≪≫
      dgKernelDerivedInfinity_mapIso_of_quasiIso R D F (BimoduleTensor.composeMap R F E D g f)
        (BimoduleTensor.composeMap_kFlat_quasiIso R F E D hP hP' g f hg hf) =
    (dgKernelDerivedInfinity_mapIso_of_quasiIso R D E f hf).postcomp
        (dgKernelDerivedInfinity R E F (BimoduleCategory.underlying R F E Q)) ≪≫
      (dgKernelDerivedInfinity_mapIso_of_quasiIso R E F g hg).precomp
        (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P')) ≪≫
      dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F
        (BimoduleCategory.underlying R E D P') (BimoduleCategory.underlying R F E Q') hP' := by
  apply Iso.ext
  simpa only [Iso.trans_hom, functorIso_postcomp_hom_typed, functorIso_precomp_hom_typed,
    dgKernelDerivedInfinity_comparison_hom, Category.assoc] using!
      dgKernelDerivedInfinity_compIso_hom_naturality R D E F f g hP hP' hQ hQ'
end
end SerrePositivity.InfinityCategories
