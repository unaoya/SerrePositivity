module
public import SerrePositivity.KST.SConstruction.DGKInputPerfectNu
public import SerrePositivity.KST.SConstruction.PerfectStableHoArrow
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategories
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity
public import Mathlib.CategoryTheory.Enriched.Basic

/-!
概要：固定 ν の同値な完全射は、同じ Cat^perf 辺の可逆な射の類を与える。
方針：同じ順逆の完全射と指定単位・余単位を、既存の Cat^perf 射の法則へ渡す。
規約：固定 S 内での逆射や K の局所化性を要求しない。
使われ方：実 dg 増大屋根の Cat^perf 像の可逆性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants

open scoped Simplicial

/-- 概要：同じ完全射の指定零次合成同型は Cat^perf の射の逆律を与える。
方針：既存の合成則・関手同型の不変性・恒等則を合わせる。
規約：元の両射を保持する。使われ方：同じ完全同値の可逆性。 -/
lemma perfectStableHoArrow_comp_eq_id_of_functorIso
    {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B A)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F.hom ≫ G.hom) (𝟙 A.obj)) :
    perfectStableHoArrow F hA hB ≫ perfectStableHoArrow G hB hA = 𝟙 _ := by
  let C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A A := ⟨F.hom ≫ G.hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp F.hom G.hom⟩
  let J : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A A := ⟨𝟙 A.obj, inferInstance⟩
  have hc := perfectStableHoArrow_comp F G hA hB hA
  change perfectStableHoArrow C hA hA =
    perfectStableHoArrow F hA hB ≫ perfectStableHoArrow G hB hA at hc
  have he : perfectStableHoArrow C hA hA = perfectStableHoArrow J hA hA :=
    perfectStableHoArrow_eq_of_functorIso hA hA e
  exact hc.symm.trans (he.trans (perfectStableHoArrow_id A hA))

/-- 概要：同じ完全同値の Cat^perf の辺の類は可逆。
方針：指定した逆関手と二つの全関手同型を射の合成則へ渡す。
規約：同じ順方向の辺を保持する。使われ方：固定 ν 辺の可逆性。 -/
lemma perfectStableHoArrow_isIso_of_isQCatEquivalence
    {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A.obj) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B.obj)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence F.hom) : IsIso (perfectStableHoArrow F hA hB) := by
  let E := hF.choose
  let G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B A := ⟨E.inv,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence E.symm.isQCatEquivalence⟩
  refine ⟨⟨perfectStableHoArrow G hB hA, ?_, ?_⟩⟩
  · exact perfectStableHoArrow_comp_eq_id_of_functorIso F G hA hB E.homInvIso
  · exact perfectStableHoArrow_comp_eq_id_of_functorIso G F hB hA E.invHomIso

variable (R : Type u) [CommRing R] {P Q : PerfDGInput.{u, v} R} (f : P ⟶ Q)

/-- 概要：固定 ν の Cat^perf 持ち上げの辺は元の完全射の同じ全一単体。
方針：元 ν の辺回収と全部分複体の包含の単射性を使用する。
規約：辺の代表を選び直さない。使われ方：同じ固定 dg 辺の像の照合。 -/
lemma dgKInputPerfectNu_edge :
    (dgKInputPerfectNu R).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge =
      (perfectStableArrow (dgKInputNuMap R f)
        (dgKInputStableValue_isIdempotentComplete R P)
        (dgKInputStableValue_isIdempotentComplete R Q)).edge := by
  apply Subtype.ext
  have h := congrArg (fun g => g.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
    (dgKInputPerfectNu_inclusion R)
  exact h.trans (dgKInputNu_edge R f)

/-- 概要：固定 ν の同値な完全射は同じ Cat^perf 像で可逆。
方針：元の辺の回収式と既存の射の類の可逆性を合わせる。
規約：S 内での同値を仮定しない。使われ方：元入力への実増大屋根。 -/
lemma dgKInputPerfectNu_map_isIso_of_isQCatEquivalence
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R P)
      (dgKInputStableValue R Q) from dgKInputNuMap R f).hom) :
    IsIso ((hoFunctor.map (dgKInputPerfectNu R)).toFunctor.map
      (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated)) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (dgKInputPerfectNu R)).toTruncated := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map
      (dgKInputPerfectNu R)).toTruncated) (f := (perfectStableArrow (dgKInputNuMap R f)
        (dgKInputStableValue_isIdempotentComplete R P)
        (dgKInputStableValue_isIdempotentComplete R Q)).toTruncated)
          (dgKInputPerfectNu_edge R f)).mpr
    exact perfectStableHoArrow_isIso_of_isQCatEquivalence _ _ _ hf
  exact he

end SerrePositivity.KST.SConstruction
