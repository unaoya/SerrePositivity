module

public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimitUniversal

/-!
概要：元の homotopy end の Kan 列は、実際の重み付き内部 Hom 図式の end である。
方針：構造可換な普遍射を使い、全段の end の射影で一意性を示す。
規約：Ω 条件・単射性・Sp の安定性は不要。使われ方：Hom と homotopy end の交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits

namespace SerrePositivity.KST.Spectra.KanSequence
variable {I : Type u} [SmallCategory I] (D : I ⥤ KanSequence.{u})

/-- 元の homotopy end の厳密な wedge は、Kan 列の圏で実際に極限。 -/
def homotopyLimitWedge_isLimit : IsLimit (homotopyLimitWedge D) :=
  Multifork.IsLimit.mk (homotopyLimitWedge D) (fun s ↦ homotopyLimitWedgeLift D s)
    (fun s i ↦ by
      apply Hom.ext_app
      intro n
      exact homotopyLimitWedgeLiftApp_π D s n i)
    (fun s m hm ↦ by
      apply Hom.ext_app
      intro n
      apply end_.hom_ext
      intro i
      have h := congrArg (fun p : s.pt ⟶
        mapping (PointedObject.adjoin ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i)) (D.obj i) ↦ p.app n)
        (hm i)
      exact h.trans (homotopyLimitWedgeLiftApp_π D s n i).symm)

/-- 重み付き内部 Hom 列の図式は、実際に end を持つ。 -/
instance weightedDiagram_hasEnd : HasEnd (weightedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D) :=
  HasLimit.mk ⟨homotopyLimitWedge D, homotopyLimitWedge_isLimit D⟩

/-- 元の段ごとの模型と、Kan 列の圏で取った実際の end の同型。 -/
def homotopyLimitEndIso :
    homotopyLimit D ≅ end_ (weightedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D) :=
  (homotopyLimitWedge_isLimit D).conePointUniqueUpToIso (limit.isLimit _)

/-- 同型を通した end の射影は、構成済みの元の厳密な射影。 -/
@[reassoc (attr := simp)]
lemma homotopyLimitEndIso_hom_π (i : I) :
    (homotopyLimitEndIso D).hom ≫ end_.π (weightedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) D) i =
      homotopyLimitEvaluation D i :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (homotopyLimitWedge_isLimit D) (limit.isLimit _) (.left i)

end SerrePositivity.KST.Spectra.KanSequence
