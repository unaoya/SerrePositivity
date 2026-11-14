module
public import SerrePositivity.KST.SConstruction.DGAlgebraEnvelopeGenerator
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeYoneda
public import SerrePositivity.KST.SConstruction.DGOdotRightAlgebraComparison
public import SerrePositivity.KST.SConstruction.DGEndInclusionPerfectGeneration
public import SerrePositivity.KST.SConstruction.DGKPerfectComposition
public import SerrePositivity.KST.SConstruction.PerfectDGMoritaEquivalence

/-! # 元の dg 代数から指定像付き小さい Perf 模型への Yoneda の Morita 性
概要：元の全 Hom Yoneda と自由生成 API により、同じ一回 Perf 延長を同値とする。
方針：同じ自由代表の End への準同値と、同じ End 包含の生成による Morita 性を合成する。
規約：元の Yoneda 射を保持し、生成性を追加仮定にしない。使われ方：具体的 ⊙ の終域比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (B : Mon (Complex R))
  (J : Type v) [Small.{u} J] (X : J → PerfectDGModule R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B))
local notation "D" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B
local notation "C" => DGSmallPerfectEnvelope R (D) J X
local notation "b" => (Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star : _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B)
local notation "Y" => dgSmallPerfectEnvelopeYoneda R (D) J X
local notation "r" => dgSmallPerfectEnvelopeRepresentable R (D) J X (b)

/-- 元の一対象圏を同じ自由代表の End へ送る、元の Yoneda による実射。 -/
def dgAlgebraEnvelopeYonedaEnd : DGFunctor R (D) (EndomorphismObject (r)) :=
  (dgAlgebraToOriginalEnd R B).comp (endomorphismMap R (Y) (b))

omit [Small.{u} J] in
/-- 同じ実射の全 Hom 作用は、元の Yoneda Hom 同型の逆射。 -/
lemma dgAlgebraEnvelopeYonedaEnd_map (x y : D) :
    (dgAlgebraEnvelopeYonedaEnd R B J X).map x y =
      (dgYonedaIso R (b) (representable R (b))).inv := by
  change 𝟙 _ ≫ (Y).map (b) (b) = _
  rw [Category.id_comp]
  rfl

/-- 元の自由代表 End への同じ実射は準同値。 -/
lemma dgAlgebraEnvelopeYonedaEnd_quasiEquivalence :
    QuasiEquivalence (dgAlgebraEnvelopeYonedaEnd R B J X) := by
  refine ⟨?_, ⟨?_⟩⟩
  · intro x y
    rw [dgAlgebraEnvelopeYonedaEnd_map]
    constructor
    intro n
    exact quasiIsoAt_of_isIso (dgYonedaIso R (b) (representable R (b))).inv n
  · intro y
    refine ⟨(toHomotopy R (D)).obj (ForgetEnrichment.of (Complex R) (b)), ⟨?_⟩⟩
    obtain ⟨y⟩ := y
    cases y using EndomorphismObject.rec
    exact Iso.refl _

omit [Small.{u} J] in
/-- 同じ End への射と包含は、元の Yoneda 関手そのものを厳密に回収する。 -/
lemma dgAlgebraEnvelopeYonedaEnd_inclusion :
    (dgAlgebraEnvelopeYonedaEnd R B J X).comp (endomorphismInclusion R (r)) = (Y) := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgAlgebraEnvelopeYonedaEnd R B J X).comp (endomorphismInclusion R (r)))
    (G := (Y)) (fun x => by obtain ⟨x⟩ := x; cases x; rfl)
  intro x y
  obtain ⟨x⟩ := x
  cases x
  obtain ⟨y⟩ := y
  cases y
  change ((𝟙 _ ≫ (Y).map (b) (b)) ≫ 𝟙 _) ≫ eqToHom (by rfl) = (Y).map (b) (b)
  rw [eqToHom_refl, Category.comp_id, Category.comp_id, Category.id_comp]

/-- 元の Yoneda の同じ一回主 Perf 延長は、指定像族によらず実際に同値。 -/
lemma dgAlgebraEnvelopeYoneda_isMorita :
    (quasiEquivalencePerfectExtension R (D) (C) (Y)).IsEquivalence := by
  letI : (quasiEquivalencePerfectExtension R (D) (EndomorphismObject (r))
      (dgAlgebraEnvelopeYonedaEnd R B J X)).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence R (D) (EndomorphismObject (r))
      (dgAlgebraEnvelopeYonedaEnd R B J X)
      (dgAlgebraEnvelopeYonedaEnd_quasiEquivalence R B J X)).isEquivalence_functor
  letI : (quasiEquivalencePerfectExtension R (EndomorphismObject (r)) (C)
      (endomorphismInclusion R (r))).IsEquivalence :=
    dgEndInclusionPerfect_isEquivalence R (C) (r)
      (dgAlgebraEnvelope_perfectOver_representable_eq R B J X (b))
  rw [← dgAlgebraEnvelopeYonedaEnd_inclusion R B J X]
  exact dgKPerfectExtension_comp_isEquivalence R (D) (EndomorphismObject (r)) (C)
    (dgAlgebraEnvelopeYonedaEnd R B J X) (endomorphismInclusion R (r))

/-- 同じ元の Yoneda の実 dg Perf 延長は、同じ全 Hom 作用の準同値。 -/
lemma dgAlgebraEnvelopeYoneda_perfectDG_quasiEquivalence :
    QuasiEquivalence (perfectDGExtension R (D) (C) (Y)) := by
  letI := dgAlgebraEnvelopeYoneda_isMorita R B J X
  exact perfectDGExtension_quasiEquivalence R (D) (C) (Y)

end SerrePositivity.KST.SConstruction
