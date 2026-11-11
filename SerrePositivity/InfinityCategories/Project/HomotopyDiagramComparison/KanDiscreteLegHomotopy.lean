module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.DiscreteConeHomotopyComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanConeLimits
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PostcompositionHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.RepresentableLimitEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-!
概要：元の Kan 離散錐の脚ごとのホモトピーは、元の native 全錐の極限性を保つ。
方針：全豊穣 Hom で同じ脚の円柱を作り、元の標準比較のホモトピー不変性を使う。
規約：頂点・図式を固定し、通常の厳密極限の普遍性は仮定しない。
使われ方：反復射影の評価を元の Kan 積射影と比較して極限性を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の Kan 図式・頂点・指定された全脚を持つ通常の離散錐。 -/
def kanDiscreteConeOfLegs {J : Type u} (F : Discrete J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (f : (i : Discrete J) → K ⟶ F.obj i) : Cone F where
  pt := K
  π := Discrete.natTrans f

/-- 元の Kan 射の円柱は、元の豊穣 Hom の後合成に同じ向きの円柱を与える。 -/
def kanHomPostcompositionHomotopy (x K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {f g : K ⟶ L}
    (H : SSet.Homotopy f g) :
    SSet.Homotopy (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj (Opposite.op x)).map f)
      (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj (Opposite.op x)).map g) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObject_sHomWhiskerLeft, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObject_sHomWhiskerLeft]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionHomotopy H x.obj

/-- 元の全脚のホモトピーは、全ての元の豊穣 Hom の標準比較へ移る。 -/
def kanDiscreteRepresentableComparisonHomotopy {J : Type u}
    (F : Discrete J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    {f g : (i : Discrete J) → K ⟶ F.obj i}
    (H : ∀ i, SSet.Homotopy (f i) (g i)) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison (kanDiscreteConeOfLegs F K f) x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.representableHomotopyLimitComparison (kanDiscreteConeOfLegs F K g) x) := by
  change SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.discreteConeOfLegs (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x)
      (SimplicialCategory.sHom x K) (fun i ↦
        ((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj (Opposite.op x)).map (f i))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.discreteConeOfLegs (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x)
      (SimplicialCategory.sHom x K) (fun i ↦
        ((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj (Opposite.op x)).map (g i))))
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.discreteHolimComparisonHomotopy _ _ (fun i ↦ kanHomPostcompositionHomotopy x K _ (H i))

/-- 元の脚ごとの Kan ホモトピーは、元の native 離散全錐の極限性を保ち反映する。 -/
lemma kanDiscreteCone_isLimit_iff_of_leg_homotopies {J : Type u}
    (F : Discrete J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    {f g : (i : Discrete J) → K ⟶ F.obj i}
    (H : ∀ i, SSet.Homotopy (f i) (g i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (kanDiscreteConeOfLegs F K f)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (kanDiscreteConeOfLegs F K g)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_iff_discrete_representableComparison,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_iff_discrete_representableComparison]
  apply forall_congr'
  intro x
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex _
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy
    (kanDiscreteRepresentableComparisonHomotopy F K H x)
  exact ⟨fun h ↦ (h.isQCatEquivalence.ofFunctorIso e).isSimplicialHomotopyEquivalence,
    fun h ↦ (h.isQCatEquivalence.ofFunctorIso e.symm).isSimplicialHomotopyEquivalence⟩

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
