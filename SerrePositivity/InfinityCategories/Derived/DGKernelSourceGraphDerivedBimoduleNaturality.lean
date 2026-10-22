module
public import SerrePositivity.InfinityCategories.Derived.DGKernelSourceGraphBimoduleNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedHomFunctor
/-!
概要：元の graph 入力変更と元の kernel の実導来作用の任意射自然性を回収する。
方針：指定 graph 比較・κ・元の双加群同型の自然性を保持する。
規約：原 kernel に平坦性を追加しない。使われ方：元の始域制限と cell 入力比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (C D E : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  [DGCategory R E] [Small.{u} E] (F : DGFunctor R C D)
lemma dgKernelDerivedInfinity_sourceGraphBimoduleIso_hom_naturality
    {P0 P1 : BimoduleCategory R E D} (g : P0 ⟶ P1) :
    (dgKernelDerivedInfinity_bimoduleIso R C E
      (dgKernelSourceGraphBimoduleIso R C D E F
        (BimoduleCategory.underlying R E D P0))).hom ≫
      (dgKernelDerivedFunctorHomFunctor R C E).map
        ((BimoduleCategory.middleLeftRestrictionFunctor R E D C F).map g) =
    (dgKernelDerivedFunctorHomFunctor R C E).map
        (BimoduleTensor.composeMap R E D C g
          (𝟙 (BimoduleCategory.of R D C (functorGraph R C D F)))) ≫
      (dgKernelDerivedInfinity_bimoduleIso R C E
        (dgKernelSourceGraphBimoduleIso R C D E F
          (BimoduleCategory.underlying R E D P1))).hom := by
  have h := congrArg (fun z => (dgKernelDerivedFunctorHomFunctor R C E).map z)
    (dgKernelSourceGraphBimoduleIso_hom_naturality R C D E F g)
  simp only [CategoryTheory.Functor.map_comp] at h
  rw [← dgKernelDerivedFunctorHomFunctor_mapIso,
    ← dgKernelDerivedFunctorHomFunctor_mapIso]
  exact h.symm
end SerrePositivity.InfinityCategories
