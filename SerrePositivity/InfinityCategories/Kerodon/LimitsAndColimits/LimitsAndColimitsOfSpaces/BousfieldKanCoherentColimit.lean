module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.BousfieldKanConeSourceRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentConeSourceApex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.BousfieldKanColimitCriterion

/-!
概要：一般の通常の小圏上の Kan 値図式の Bousfield–Kan coend は、実際の ∞ 余極限を与える。
方針：反対錐全体の明示的な Hom の族の頂点と制限を照合し、極限判定を双対化する。
規約：任意の coherent な添字単体集合への拡張は別途必要。通常の小圏と strict 図式を扱う。
使われ方：HTT 4.2.4.1 の余極限側、𝒮 の一般の小圏で添字付けた余極限。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
variable {I : Type u} [SmallCategory I]

local instance bkColimitOppositeHomKan (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ) :
    KanComplex (SimplicialCategory.sHom X Y) :=
  inferInstanceAs (KanComplex (SimplicialCategory.sHom Y.unop X.unop))

/-- Kan coend の反対錐は、元の反対図式上の実際の ∞ 極限錐である。 -/
lemma bousfieldKanCoherentOppositeCone_isLimit (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone F) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone_isLimit_of_comparison_lifts F
    (fun Y ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceFamily (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone F)
      (Opposite.op (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanReflectedBousfieldKanColimitObject F))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone_vertex F) (Opposite.op Y))
  · intro Y
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentConeSourceFamily_evaluation _ _ _ _
  · intro Y
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentConeSourceFamily_restrict F Y

/-- Kan 置換した反転 coend の native な余錐は、元の図式の ∞ 余極限余錐である。 -/
lemma bousfieldKanCoherentCocone_isColimit (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentCocone F) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentCocone]
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff _ _).1
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff _ _).1
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconePost_isColimit_iff _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentOppositeReturnIso _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).hom).1
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_reverseCocone_restrict (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentOppositeCone F)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictCoconeIndexIso.{u, u + 1} I).hom).1
      (bousfieldKanCoherentOppositeCone_isLimit F)

/-- 任意の通常の小圏の Kan 値図式の coherent nerve は、𝒮 内に余極限を持つ。 -/
lemma kanDiagramCoherentNerve_hasColimit (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.bousfieldKanCoherentCocone F, bousfieldKanCoherentCocone_isColimit F⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
