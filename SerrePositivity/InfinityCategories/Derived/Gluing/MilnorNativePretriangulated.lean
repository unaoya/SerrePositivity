module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorResolvedVerdier
public import SerrePositivity.InfinityCategories.Derived.Gluing.Pretriangulated
public import SerrePositivity.InfinityCategories.Derived.SmallPerfectDGPretriangulated
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedQuasiEquivalenceForward
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedFunctorExact
/-!
概要：元 Milnor 小 Perf 模型の前三角性と元対角の完全性を無条件で接続する。
方針：D-18 の小模型の前三角性を同じ準同値包含で順方向へ運ぶ。
規約：元の対象・全 Hom・対角を保持し、全 Perf の Small 性を要求しない。
使われ方：cell 平坦商の実 Verdier 列から前三角性・完全性の明示入力を除く。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.SConstruction KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
lemma dgGluingMilnorSource_isDGPretriangulated :
    IsDGPretriangulated R (DGSmallPerfectBase R (dgAlgebraCategory R d.source)) := by
  let := smallPerfectDGModuleOver_isDGPretriangulated R (dgAlgebraCategory R d.source) Set.univ
  exact isDGPretriangulated_of_quasiEquivalence_forward R _ _
    (dgSmallPerfectEnvelopeSmallInclusion R (dgAlgebraCategory R d.source) Empty
      (dgSmallPerfectBaseFamily R (dgAlgebraCategory R d.source)))
    (dgSmallPerfectEnvelopeSmallInclusion_quasiEquivalence R _ _ _)
lemma dgGluingMilnorLeft_isDGPretriangulated :
    IsDGPretriangulated R (DGSmallPerfectArrowTarget R (dgAlgebraCategory R d.source)
      (dgAlgebraCategory R d.left) (dgAlgebraMap R d.top)) := by
  let := smallPerfectDGModuleOver_isDGPretriangulated R (dgAlgebraCategory R d.left) Set.univ
  exact isDGPretriangulated_of_quasiEquivalence_forward R _ _
    (dgSmallPerfectEnvelopeSmallInclusion R (dgAlgebraCategory R d.left)
      (DGSmallPerfectBase R (dgAlgebraCategory R d.source))
      (dgSmallPerfectEnvelopeExtensionFamily R _ _ Empty (dgSmallPerfectBaseFamily R _)
        (dgAlgebraMap R d.top)))
    (dgSmallPerfectEnvelopeSmallInclusion_quasiEquivalence R _ _ _)
lemma dgGluingMilnorRight_isDGPretriangulated :
    IsDGPretriangulated R (DGSmallPerfectArrowTarget R (dgAlgebraCategory R d.source)
      (dgAlgebraCategory R d.right) (dgAlgebraMap R d.side)) := by
  let := smallPerfectDGModuleOver_isDGPretriangulated R (dgAlgebraCategory R d.right) Set.univ
  exact isDGPretriangulated_of_quasiEquivalence_forward R _ _
    (dgSmallPerfectEnvelopeSmallInclusion R (dgAlgebraCategory R d.right)
      (DGSmallPerfectBase R (dgAlgebraCategory R d.source))
      (dgSmallPerfectEnvelopeExtensionFamily R _ _ Empty (dgSmallPerfectBaseFamily R _)
        (dgAlgebraMap R d.side)))
    (dgSmallPerfectEnvelopeSmallInclusion_quasiEquivalence R _ _ _)
lemma dgGluingMilnor_isDGPretriangulated : IsDGPretriangulated R (DGOdotGluing R d) :=
  dgGluing_isDGPretriangulated R _ _ _
    (dgGluingMilnorLeft_isDGPretriangulated R d)
    (dgGluingMilnorRight_isDGPretriangulated R d)
lemma dgGluingMilnorNativeDiagonal_isExactFunctor :
    IsExactFunctor (dgNerve.map (dgOdotQuotientInput R d).diagonal) := by
  let := dgGluingMilnorSource_isDGPretriangulated R d
  let := dgGluingMilnor_isDGPretriangulated R d
  exact dgPretriangulatedFunctor_isExactFunctor R _ _ _
local instance : IsDGPretriangulated R (DGOdotGluing R d) :=
  dgGluingMilnor_isDGPretriangulated R d
local instance : IsExactFunctor (dgNerve.map (dgOdotQuotientInput R d).diagonal) :=
  dgGluingMilnorNativeDiagonal_isExactFunctor R d
theorem dgGluingMilnor_isResolvedVerdierSequence_of_generation
    (h : DGGluingMilnorSquare R d) (hgen : DGGluingMilnorSmallPerfectGeneration R d) :
    IsVerdierSequence (dgGluingMilnorNativeDiagonal R d)
      (dgGluingMilnorResolvedProjection R d) :=
  dgGluingMilnor_isResolvedVerdierSequence R d h hgen
end SerrePositivity.InfinityCategories
