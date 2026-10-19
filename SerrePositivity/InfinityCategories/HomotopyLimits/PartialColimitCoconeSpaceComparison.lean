module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitSpanHomEnd

/-!
概要：元の coherent 図式と部分余極限対象の span の固定終点余錐空間を実際の射で比較する。
方針：共通の左 Hom の end を通し、span 側の比較のホモトピー逆を選ぶ。
規約：余錐の普遍点の保存は別途必要。使われ方：余極限の貼り合わせの写像空間側の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (hB : IsColimitCone dB)
  (dC : JoinCocone (j ≫ p)) (hC : IsColimitCone dC) (y : SpaceInfinity.{u} _⦋0⦌)

/-- 共通の左 Hom の end から、実際の span の余錐空間へのホモトピー逆を選ぶ。 -/
def partialColimitSpanHomEndRetraction :
    weightedSections (bousfieldKanWeight (AsSmall.{u + 1} WalkingCospan))
        (partialColimitHomCospan hp p y c hc dB dC) ⟶
      coconeMappingSpace (strictCoherentDiagram
        (partialColimitApexSpan c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)) y :=
  (partialColimitSpanCoconeToHomEnd_homotopyEquivalence hp p c hc dB dC y).choose

/-- 選んだ逆も、実際の span の余錐空間へのホモトピー同値。 -/
lemma partialColimitSpanHomEndRetraction_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (partialColimitSpanHomEndRetraction hp p c hc dB dC y) := by
  let h := partialColimitSpanCoconeToHomEnd_homotopyEquivalence hp p c hc dB dC y
  exact ⟨partialColimitSpanCoconeToHomEnd hp p c hc dB dC y, h.choose_spec.2, h.choose_spec.1⟩

/-- 元の固定終点余錐空間から、部分余極限頂点の実際の span の余錐空間への射。 -/
def partialColimitOriginalToSpanCocones :
    coconeMappingSpace p y ⟶
      coconeMappingSpace (strictCoherentDiagram
        (partialColimitApexSpan c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)) y :=
  partialColimitCoconeToHomEnd hp p y c hc dB hB dC hC ≫
    partialColimitSpanHomEndRetraction hp p c hc dB dC y

/-- 境界の一方が単射なら、元の図式と部分余極限 span の余錐空間は実際にホモトピー同値。 -/
lemma partialColimitOriginalToSpanCocones_homotopyEquivalence [Mono g] :
    IsSimplicialHomotopyEquivalence
      (partialColimitOriginalToSpanCocones hp p c hc dB hB dC hC y) := by
  have : KanComplex (coconeMappingSpace p y) := coconeMappingSpace_kanComplex _ _
  exact (partialColimitCoconeToHomEnd_homotopyEquivalence hp p y c hc dB hB dC hC).comp
    (partialColimitSpanHomEndRetraction_homotopyEquivalence hp p c hc dB dC y)

/-- span への比較を共通 end へ戻すと、元の図式側の比較射と全単体でホモトピック。 -/
lemma partialColimitOriginalToSpanCocones_end_homotopy :
    Nonempty (SSet.Homotopy
      (partialColimitOriginalToSpanCocones hp p c hc dB hB dC hC y ≫
        partialColimitSpanCoconeToHomEnd hp p c hc dB dC y)
      (partialColimitCoconeToHomEnd hp p y c hc dB hB dC hC)) := by
  let h := partialColimitSpanCoconeToHomEnd_homotopyEquivalence hp p c hc dB dC y
  obtain ⟨H⟩ := h.choose_spec.2
  have hh := functorHomotopyPrecomp H
    (partialColimitCoconeToHomEnd hp p y c hc dB hB dC hC)
  simpa only [partialColimitOriginalToSpanCocones, partialColimitSpanHomEndRetraction,
    Category.assoc, Category.comp_id] using (show Nonempty (SSet.Homotopy _ _) from ⟨hh⟩)

/-- 同じ比較を、Kan 値図式の既存の native な coherent nerve の表示で公開する。 -/
def partialColimitOriginalToNativeSpanCocones :
    coconeMappingSpace p y ⟶
      coconeMappingSpace (kanDiagramCoherentNerve
        (partialColimitApexSpan c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)) y :=
  partialColimitOriginalToSpanCocones hp p c hc dB hB dC hC y ≫
    eqToHom (congrArg (fun t ↦ coconeMappingSpace t y)
      (strictCoherentDiagram_eq_kanDiagram _))

/-- native な表示でも、元の図式と部分余極限 span の余錐空間の比較はホモトピー同値。 -/
lemma partialColimitOriginalToNativeSpanCocones_homotopyEquivalence [Mono g] :
    IsSimplicialHomotopyEquivalence
      (partialColimitOriginalToNativeSpanCocones hp p c hc dB hB dC hC y) := by
  have : KanComplex (coconeMappingSpace p y) := coconeMappingSpace_kanComplex _ _
  exact (partialColimitOriginalToSpanCocones_homotopyEquivalence hp p c hc dB hB dC hC y).comp
    (homotopyEquivalence_of_isIso _)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
