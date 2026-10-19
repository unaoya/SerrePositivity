module

public import SerrePositivity.InfinityCategories.HomotopyLimits.BousfieldKanConeSourceRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentConeSourceApex
public import SerrePositivity.InfinityCategories.HomotopyLimits.BousfieldKanColimitCriterion

/-!
概要：一般の通常の小圏上の Kan 値図式の Bousfield–Kan coend は、実際の ∞ 余極限を与える。
方針：反対錐全体の明示的な Hom の族の頂点と制限を照合し、極限判定を双対化する。
規約：任意の coherent な添字単体集合への拡張は別途必要。通常の小圏と strict 図式を扱う。
使われ方：HTT 4.2.4.1 の余極限側、𝒮 の一般の小圏で添字付けた余極限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {I : Type u} [SmallCategory I]

local instance bkColimitOppositeHomKan (X Y : KanObject.{u}ᵒᵖ) :
    KanComplex (SimplicialCategory.sHom X Y) :=
  inferInstanceAs (KanComplex (SimplicialCategory.sHom Y.unop X.unop))

/-- Kan coend の反対錐は、元の反対図式上の実際の ∞ 極限錐である。 -/
lemma bousfieldKanCoherentOppositeCone_isLimit (F : I ⥤ KanObject.{u}) :
    IsLimitCone (bousfieldKanCoherentOppositeCone F) := by
  apply bousfieldKanCoherentOppositeCone_isLimit_of_comparison_lifts F
    (fun Y ↦ coherentConeSourceFamily (bousfieldKanCoherentOppositeCone F)
      (Opposite.op (kanReflectedBousfieldKanColimitObject F))
      (bousfieldKanCoherentOppositeCone_vertex F) (Opposite.op Y))
  · intro Y
    exact coherentConeSourceFamily_evaluation _ _ _ _
  · intro Y
    exact bousfieldKanCoherentConeSourceFamily_restrict F Y

/-- Kan 置換した反転 coend の native な余錐は、元の図式の ∞ 余極限余錐である。 -/
lemma bousfieldKanCoherentCocone_isColimit (F : I ⥤ KanObject.{u}) :
    IsColimitCone (bousfieldKanCoherentCocone F) := by
  rw [bousfieldKanCoherentCocone]
  apply (coherentCoconeOfDiagramEq_isColimit_iff _ _).1
  apply (coherentCoconeOfDiagramEq_isColimit_iff _ _).1
  apply (coherentCoconePost_isColimit_iff _ (coherentOppositeReturnIso KanObject.{u}).hom).1
  exact (isLimitCone_iff_reverseCocone_restrict (bousfieldKanCoherentOppositeCone F)
    (strictCoconeIndexIso.{u, u + 1} I).hom).1
      (bousfieldKanCoherentOppositeCone_isLimit F)

/-- 任意の通常の小圏の Kan 値図式の coherent nerve は、𝒮 内に余極限を持つ。 -/
lemma kanDiagramCoherentNerve_hasColimit (F : I ⥤ KanObject.{u}) :
    HasColimit (kanDiagramCoherentNerve F) :=
  ⟨bousfieldKanCoherentCocone F, bousfieldKanCoherentCocone_isColimit F⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
