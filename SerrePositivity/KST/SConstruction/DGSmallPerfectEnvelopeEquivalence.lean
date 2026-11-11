module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelope
public import SerrePositivity.KST.SConstruction.PerfectDGStableModel
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 指定延長像を保持した小さい Perf 模型の準同値
概要：元の小代表系を含む模型の包含は準同値であり、元の全 Perf の安定性を反映する。
方針：全 Hom 恒等射と、小代表系の既存 H⁰ 本質的全射性を使う。
規約：指定延長像を選び直さない。使われ方：実 LT 入力の小さい安定 dg 模型。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (J : Type w) (X : J → PerfectDGModule R D)
local notation "C" => DGSmallPerfectEnvelope R D J X
local notation "I" => dgSmallPerfectEnvelopeInclusion R D J X

/-- 元の小代表系から拡張模型への、同じ対象と全 Hom を保つ厳密 dg 包含。 -/
def dgSmallPerfectEnvelopeSmallInclusion :
    DGFunctor R (SmallPerfectDGModuleOver R D Set.univ) (C) :=
  (DGFunctor.id (A := R) (PerfectDGModule R D)).restrict
    (Set.range (perfectDGModuleRepresentative R D Set.univ))
    (dgSmallPerfectEnvelopeObjects R D J X)
    (fun x hx => Or.inl ⟨⟨x, hx⟩, rfl⟩)

/-- 拡張模型から元の全 Perf への包含は、同じ全 Hom で準同型を持つ。 -/
lemma dgSmallPerfectEnvelopeInclusion_homQuasiIso : HomQuasiIso (I) := by
  intro x y
  change QuasiIso (𝟙 _)
  constructor
  intro n
  exact quasiIsoAt_of_isIso (𝟙 _) n

/-- 指定延長像を加えた同じ実模型の包含は H⁰ で本質的全射。 -/
lemma dgSmallPerfectEnvelopeInclusion_essSurj : (I).onHomotopy.EssSurj := by
  let F := dgSmallPerfectEnvelopeSmallInclusion R D J X
  refine ⟨fun Y => ?_⟩
  let := (smallPerfectDGModuleInclusion_quasiEquivalence R D Set.univ).2
  obtain ⟨Z, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (smallPerfectDGModuleInclusion R D Set.univ).onHomotopy Y
  refine ⟨F.onHomotopy.obj Z, ⟨?_⟩⟩
  exact e

/-- 元の全 Perf への同じ実 dg 包含は準同値。 -/
lemma dgSmallPerfectEnvelopeInclusion_quasiEquivalence : QuasiEquivalence (I) :=
  ⟨dgSmallPerfectEnvelopeInclusion_homQuasiIso R D J X,
    dgSmallPerfectEnvelopeInclusion_essSurj R D J X⟩

/-- 元の小代表系から拡張模型への包含も、全 Hom で恒等準同型を持つ。 -/
lemma dgSmallPerfectEnvelopeSmallInclusion_homQuasiIso :
    HomQuasiIso (dgSmallPerfectEnvelopeSmallInclusion R D J X) := by
  intro x y
  change QuasiIso (𝟙 _)
  constructor
  intro n
  exact quasiIsoAt_of_isIso (𝟙 _) n

/-- 元の小代表系から拡張模型への包含は H⁰ で本質的全射。 -/
lemma dgSmallPerfectEnvelopeSmallInclusion_essSurj :
    (dgSmallPerfectEnvelopeSmallInclusion R D J X).onHomotopy.EssSurj := by
  let hI : ∀ x y, IsIso ((I).map x y) := by
    intro x y
    change IsIso (𝟙 _)
    infer_instance
  let : (I).onHomotopy.Full := (I).onHomotopy_full_of_homIso hI
  let : (I).onHomotopy.Faithful := (I).onHomotopy_faithful_of_homIso hI
  let := (smallPerfectDGModuleInclusion_quasiEquivalence R D Set.univ).2
  refine ⟨fun Y => ?_⟩
  obtain ⟨Z, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (smallPerfectDGModuleInclusion R D Set.univ).onHomotopy ((I).onHomotopy.obj Y)
  exact ⟨Z, ⟨(I).onHomotopy.preimageIso e⟩⟩

/-- 元の小代表系と指定延長像を含む模型は、同じ実包含により準同値。 -/
lemma dgSmallPerfectEnvelopeSmallInclusion_quasiEquivalence :
    QuasiEquivalence (dgSmallPerfectEnvelopeSmallInclusion R D J X) :=
  ⟨dgSmallPerfectEnvelopeSmallInclusion_homQuasiIso R D J X,
    dgSmallPerfectEnvelopeSmallInclusion_essSurj R D J X⟩

/-- 同じ実 dg 包含から得る、元の全 Perf nerve との全写像空間の同値。 -/
def dgSmallPerfectEnvelopeNerveEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R D)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuasiEquivalenceNerveEquivalence (I)
    (dgSmallPerfectEnvelopeInclusion_quasiEquivalence R D J X)

/-- 元の全 Perf の安定性を、指定延長像を保持する模型へ戻す。 -/
lemma dgSmallPerfectEnvelopeNerve_isStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (C)) :=
  (dgSmallPerfectEnvelopeNerveEquivalence R D J X).isStable_iff.mpr
    (perfectDGStableModel R D Set.univ).stable

end SerrePositivity.KST.SConstruction
