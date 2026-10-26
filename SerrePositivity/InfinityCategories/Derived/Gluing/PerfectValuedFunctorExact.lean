module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectFunctorImage
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeEquivalence
public import SerrePositivity.InfinityCategories.Derived.SmallPerfectDGPretriangulated
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedQuasiEquivalenceForward
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedFunctorExact
public import SerrePositivity.InfinityCategories.Stable.EquivalenceStability
/-!
概要：小さい前三角 dg 圏から実 Perf への dg 関手の native 完全性。
方針：元の全像小包絡への厳密因子化と、その実包含同値を使う。
規約：全 Perf の Small 性を仮定しない。使われ方：元 cone 関手の完全性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C E : Type (u + 1))
  [DGCategory R C] [Small.{u} C] [DGCategory R E] [Small.{u} E]
  (F : DGFunctor R C (PerfectDGModule R E))

lemma dgPerfectValuedFunctorImage_pretriangulated :
    IsDGPretriangulated R (DGSmallPerfectFunctorImage R C E F) := by
  letI := smallPerfectDGModuleOver_isDGPretriangulated R E Set.univ
  exact isDGPretriangulated_of_quasiEquivalence_forward R _ _
    (dgSmallPerfectEnvelopeSmallInclusion R E C F.obj)
    (dgSmallPerfectEnvelopeSmallInclusion_quasiEquivalence R E C F.obj)

lemma dgPerfectValuedFunctor_isExactFunctor [IsDGPretriangulated R C] :
    IsExactFunctor (dgNerve.map F) := by
  letI := dgPerfectValuedFunctorImage_pretriangulated R C E F
  letI : IsExactFunctor (dgNerve.map (dgSmallPerfectFunctorImageLift R C E F)) :=
    dgPretriangulatedFunctor_isExactFunctor R C (DGSmallPerfectFunctorImage R C E F)
      (dgSmallPerfectFunctorImageLift R C E F)
  letI : IsExactFunctor (dgNerve.map (dgSmallPerfectEnvelopeInclusion R E C F.obj)) :=
    isExactFunctor_of_isQCatEquivalence
      (dgSmallPerfectEnvelopeNerveEquivalence R E C F.obj).isQCatEquivalence
  rw [← dgSmallPerfectFunctorImageLift_inclusion R C E F, dgNerve.map_comp]
  exact isExactFunctor_comp _ _

end SerrePositivity.InfinityCategories
