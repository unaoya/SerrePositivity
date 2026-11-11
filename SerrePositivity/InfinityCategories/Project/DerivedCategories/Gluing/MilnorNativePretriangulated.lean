module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.MilnorResolvedVerdier
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Pretriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SmallPerfectDGPretriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedQuasiEquivalenceForward
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedFunctorExact
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet KST.SConstruction KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
lemma dgGluingMilnorSource_isDGPretriangulated :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectDGModuleOver_isDGPretriangulated R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source) Set.univ
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_quasiEquivalence_forward R _ _
    (dgSmallPerfectEnvelopeSmallInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source) Empty
      (dgSmallPerfectBaseFamily R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source)))
    (dgSmallPerfectEnvelopeSmallInclusion_quasiEquivalence R _ _ _)
lemma dgGluingMilnorLeft_isDGPretriangulated :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGSmallPerfectArrowTarget R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectDGModuleOver_isDGPretriangulated R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left) Set.univ
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_quasiEquivalence_forward R _ _
    (dgSmallPerfectEnvelopeSmallInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left)
      (DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source))
      (dgSmallPerfectEnvelopeExtensionFamily R _ _ Empty (dgSmallPerfectBaseFamily R _)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top)))
    (dgSmallPerfectEnvelopeSmallInclusion_quasiEquivalence R _ _ _)
lemma dgGluingMilnorRight_isDGPretriangulated :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGSmallPerfectArrowTarget R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.smallPerfectDGModuleOver_isDGPretriangulated R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right) Set.univ
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isDGPretriangulated_of_quasiEquivalence_forward R _ _
    (dgSmallPerfectEnvelopeSmallInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right)
      (DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source))
      (dgSmallPerfectEnvelopeExtensionFamily R _ _ Empty (dgSmallPerfectBaseFamily R _)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side)))
    (dgSmallPerfectEnvelopeSmallInclusion_quasiEquivalence R _ _ _)
lemma dgGluingMilnor_isDGPretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluing_isDGPretriangulated R _ _ _
    (dgGluingMilnorLeft_isDGPretriangulated R d)
    (dgGluingMilnorRight_isDGPretriangulated R d)
lemma dgGluingMilnorNativeDiagonal_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal) := by
  let := dgGluingMilnorSource_isDGPretriangulated R d
  let := dgGluingMilnor_isDGPretriangulated R d
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedFunctor_isExactFunctor R _ _ _
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  dgGluingMilnor_isDGPretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal) :=
  dgGluingMilnorNativeDiagonal_isExactFunctor R d
theorem dgGluingMilnor_isResolvedVerdierSequence_of_generation
    (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) (hgen : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSmallPerfectGeneration R d) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeDiagonal R d)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedProjection R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isResolvedVerdierSequence R d h hgen
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
