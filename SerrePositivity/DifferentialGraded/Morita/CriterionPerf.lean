module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfFullHomCriterion

/-! # 一般 kernel の Perf 上の Morita 判定

列の perfect 性、全 Hom 複体の擬同型比較、列の厚い生成性の三条件と、実際の
主導来作用が Perf 上の同値であることの証拠との必要十分条件。一般右随伴を使わない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)

/-- 三つの独立した条件から、実際の主作用に一致する Perf 同値を構成する。 -/
def criterionPerfEquivalenceOfConditions (h : CriterionPerfConditions A D E K) :
    CriterionPerfEquivalenceWitness A D E K := by
  let hFF := criterionPerfFullyFaithfulOfRepresentables A D E K h.columnsPerfect
    ((criterionPerfKernelFullHomQuasiIso_iff_representableMaps A D E K).1 h.fullHomQuasiIso)
  let := hFF.full
  let := hFF.faithful
  exact criterionPerfEquivalenceWitnessOfFullyFaithful A D E K
    h.columnsPerfect h.columnsThickGenerate

variable (W : CriterionPerfEquivalenceWitness A D E K)
include W

/-- 実際の Perf 同値の必要条件として、全 Hom 複体の比較は擬同型である。 -/
lemma CriterionPerfEquivalenceWitness.fullHomQuasiIso :
    criterionPerfKernelFullHomQuasiIso A D E K := by
  apply (criterionPerfKernelFullHomQuasiIso_iff_representableMaps A D E K).2
  let := W.actionIsEquivalence A D E K
  let F := perfectDerivedKernelAction A D E K (W.columnsPerfect A D E K)
  intro d d' m n
  let X : PerfectModuleCategory A D :=
    ⟨(criterionPerfRepresentable A D d)⟦m⟧,
      (modulePerfect A D).le_shift m _
        (modulePerfectOver_representable A D d (Set.mem_univ d))⟩
  let Y : PerfectModuleCategory A D :=
    ⟨(criterionPerfRepresentable A D d')⟦n⟧,
      (modulePerfect A D).le_shift n _
        (modulePerfectOver_representable A D d' (Set.mem_univ d'))⟩
  constructor
  · intro f g he
    have h : F.map (ObjectProperty.homMk (X := X) (Y := Y) f) =
        F.map (ObjectProperty.homMk (X := X) (Y := Y) g) :=
      (modulePerfect A E).hom_ext he
    exact congrArg (fun k => k.hom) (F.map_injective h)
  · intro f
    obtain ⟨g, hg⟩ := F.map_surjective (ObjectProperty.homMk (X := F.obj X) (Y := F.obj Y) f)
    exact ⟨g.hom, congrArg (fun k => k.hom) hg⟩

/-- Perf 同値なら、列の perfect 性・全 Hom 複体比較・厚い生成性の三条件が必要。 -/
theorem CriterionPerfEquivalenceWitness.conditions : CriterionPerfConditions A D E K :=
  ⟨W.columnsPerfect A D E K, W.fullHomQuasiIso A D E K, W.columnsThickGenerate A D E K⟩

omit W in
/-- 一般 kernel の Perf Morita 判定。三条件のいずれにも他の二条件を含めない。 -/
theorem criterionPerfMorita_iff :
    CriterionPerfConditions A D E K ↔ Nonempty (CriterionPerfEquivalenceWitness A D E K) :=
  ⟨fun h => ⟨criterionPerfEquivalenceOfConditions A D E K h⟩,
    fun ⟨W⟩ => W.conditions A D E K⟩

omit W in
/-- 列の perfect 性を指定した場合の、実際の Perf 制限についての判定。 -/
theorem criterionPerfAction_isEquivalence_iff (hK : kernelColumnsPerfect A D E K) :
    (perfectDerivedKernelAction A D E K hK).IsEquivalence ↔
      criterionPerfKernelFullHomQuasiIso A D E K ∧ criterionPerfColumnsThickGenerate A D E K := by
  constructor
  · intro h
    let W : CriterionPerfEquivalenceWitness A D E K :=
      ⟨(perfectDerivedKernelAction A D E K hK).asEquivalence,
        (perfectDerivedKernelActionInclusionIso A D E K hK).symm⟩
    exact ⟨W.fullHomQuasiIso A D E K, W.columnsThickGenerate A D E K⟩
  · rintro ⟨hHom, hgen⟩
    let W := criterionPerfEquivalenceOfConditions A D E K ⟨hK, hHom, hgen⟩
    exact W.actionIsEquivalence A D E K

end SerrePositivity.DifferentialGraded.Morita
