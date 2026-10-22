module
public import SerrePositivity.InfinityCategories.Derived.DGKernelSourceGraphInfinityNaturality
public import
  SerrePositivity.InfinityCategories.Derived.DGKernelSourceGraphDerivedBimoduleNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelSourceRestrictionInfinity
/-!
概要：元の始域制限比較そのものの、任意の双加群射に対する自然性を証明する。
方針：元の source graph 比較と元の graph 合成双加群同型の二つの四角形を接続する。
規約：原 kernel の平坦性を要求しない。使われ方：cell 入力比較の全関手整合性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (C D E : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  [DGCategory R E] [Small.{u} E] (F : DGFunctor R C D)
lemma dgKernelDerivedInfinity_sourceRestrictionIso_hom_naturality
    {P0 P1 : BimoduleCategory R E D} (g : P0 ⟶ P1) :
    (dgKernelDerivedInfinity_sourceRestrictionIso R C D E F
        (BimoduleCategory.underlying R E D P0)).hom ≫
      (dgKernelDerivedFunctorHomFunctor R C E).map
        ((BimoduleCategory.middleLeftRestrictionFunctor R E D C F).map g) =
    functorHomPrecomp
      (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P0))
      (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P1))
      (dgModuleExtensionInfinity R C D F)
      ((dgKernelDerivedFunctorHomFunctor R D E).map g) ≫
      (dgKernelDerivedInfinity_sourceRestrictionIso R C D E F
        (BimoduleCategory.underlying R E D P1)).hom := by
  exact functorIso_trans_hom_square
    (dgKernelDerivedInfinity_sourceGraphIso R C D E F
      (BimoduleCategory.underlying R E D P0))
    (dgKernelDerivedInfinity_sourceGraphIso R C D E F
      (BimoduleCategory.underlying R E D P1))
    (dgKernelDerivedInfinity_bimoduleIso R C E
      (dgKernelSourceGraphBimoduleIso R C D E F (BimoduleCategory.underlying R E D P0)))
    (dgKernelDerivedInfinity_bimoduleIso R C E
      (dgKernelSourceGraphBimoduleIso R C D E F (BimoduleCategory.underlying R E D P1)))
    (functorHomPrecomp
      (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P0))
      (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P1))
      (dgModuleExtensionInfinity R C D F)
      ((dgKernelDerivedFunctorHomFunctor R D E).map g))
    ((dgKernelDerivedFunctorHomFunctor R C E).map
      (BimoduleTensor.composeMap R E D C g
        (𝟙 (BimoduleCategory.of R D C (functorGraph R C D F)))))
    ((dgKernelDerivedFunctorHomFunctor R C E).map
      ((BimoduleCategory.middleLeftRestrictionFunctor R E D C F).map g))
    (dgKernelDerivedInfinity_sourceGraphIso_hom_naturality R C D E F g)
    (dgKernelDerivedInfinity_sourceGraphBimoduleIso_hom_naturality R C D E F g)
end
end SerrePositivity.InfinityCategories
