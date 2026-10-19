module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedColimitHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.BousfieldKan
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanSourceReplacement

/-!
概要：一般の小図式の Bousfield–Kan coend と、その Kan 置換の写像空間を構成する。
方針：Iᵒᵖ 上の既存の重みを用い、coend と end の内部 Hom 同型を特殊化する。
規約：実際の対象と Hom 比較を公開する。native な coherent 余錐と余極限性は別の証明対象。
使われ方：HTT 4.2.4.1、γ3c の一般の余極限候補を coherent な普遍性へ接続する入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- 任意の小図式の反変 Bousfield–Kan 重みによる coend。 -/
def bousfieldKanColimit (F : I ⥤ SSet.{u}) : SSet.{u} :=
  weightedColimit (bousfieldKanWeight Iᵒᵖ) F

/-- Bousfield–Kan coend の内部 Hom は反変 Hom 図式の既存の end に同型。 -/
def bousfieldKanColimitHomIso (F : I ⥤ SSet.{u}) (Y : SSet.{u}) :
    (ihom (bousfieldKanColimit F)).obj Y ≅ bousfieldKanHolim (weightedColimitHomDiagram F Y) :=
  weightedColimitHomIso (bousfieldKanWeight Iᵒᵖ) F Y

/-- 任意の小さい Kan 値図式の coend を実際に Kan 置換した対象。 -/
def kanBousfieldKanColimitObject (F : I ⥤ KanObject.{u}) : KanObject.{u} :=
  anodyneKanObject (bousfieldKanColimit (F ⋙ kanObjectForget))

/-- 反変 Hom 係数は既存の反対圏の豊穣 Hom 図式と一致する。 -/
lemma kanBousfieldKanColimitHomDiagram_eq (F : I ⥤ KanObject.{u}) (Y : KanObject.{u}) :
    weightedColimitHomDiagram (F ⋙ kanObjectForget) Y.obj =
      simplicialHomDiagram F.op (Opposite.op Y) := by
  unfold simplicialHomDiagram
  rw [kanObjectOppositeHomFunctor_eq Y]
  rfl

/-- coend の Hom 同型を、Kan 値図式の反変豊穣 Hom の end に合わせる。 -/
def kanBousfieldKanColimitUnderlyingHomIso (F : I ⥤ KanObject.{u}) (Y : KanObject.{u}) :
    (ihom (bousfieldKanColimit (F ⋙ kanObjectForget))).obj Y.obj ≅
      bousfieldKanHolim (simplicialHomDiagram F.op (Opposite.op Y)) :=
  bousfieldKanColimitHomIso (F ⋙ kanObjectForget) Y.obj ≪≫
    eqToIso (congrArg bousfieldKanHolim (kanBousfieldKanColimitHomDiagram_eq F Y))

/-- Kan 置換後の Hom から一般の反変豊穣 Hom の end への実際の比較。 -/
def kanBousfieldKanColimitHomComparison (F : I ⥤ KanObject.{u}) (Y : KanObject.{u}) :
    SimplicialCategory.sHom (kanBousfieldKanColimitObject F) Y ⟶
      bousfieldKanHolim (simplicialHomDiagram F.op (Opposite.op Y)) :=
  (pre (anodyneKanObjectUnit (bousfieldKanColimit (F ⋙ kanObjectForget)))).app Y.obj ≫
    (kanBousfieldKanColimitUnderlyingHomIso F Y).hom

/-- Kan 置換後の写像空間は、一般の小図式の反変 Hom の end とホモトピー同値。 -/
lemma kanBousfieldKanColimitHomComparison_homotopyEquivalence
    (F : I ⥤ KanObject.{u}) (Y : KanObject.{u}) :
    IsSimplicialHomotopyEquivalence (kanBousfieldKanColimitHomComparison F Y) := by
  have : ∀ i, KanComplex ((simplicialHomDiagram F.op (Opposite.op Y)).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom (F.obj i.unop) Y))
  have := bousfieldKanHolim_kanComplex (simplicialHomDiagram F.op (Opposite.op Y))
  exact (homotopyEquivalence_pre_of_anodyne _ (anodyneKanObjectUnit_anodyne _) Y.obj).comp
    (homotopyEquivalence_of_isIso (kanBousfieldKanColimitUnderlyingHomIso F Y).hom)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
