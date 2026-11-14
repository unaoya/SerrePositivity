module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedHomHolimComparison

/-!
概要：反転豊穣 Hom への指定 BK 自然変換から、同じ頂点の実 join 錐を作る。
方針：重み付き end の零単体を既存の錐切断比較へ送り、指定頂点の全単射で戻す。
規約：極限性を仮定せず、錐の全高次単体と頂点を指定する。
使われ方：HA 1.2.4、G10 の明示的 Tot 錐の native な表現。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
variable (F : I ⥤ C) (x : C)
variable (φ : bousfieldKanWeight I ⟶ simplicialHomDiagram F x ⋙ SSet.opFunctor)

/-- 指定 BK 自然変換の、元の頂点での錐切断空間の点。 -/
def reflectedWeightedConeSectionPoint :
    (coherentConeSectionSpace (strictCoherentDiagram F) (coherentNerveVertex x)) _⦋0⦌ :=
  (reflectedHomHolimConeComparison F x).app (Opposite.op ⦋0⦌)
    (ULift.up (SSet.yonedaEquiv (weightedSectionsLift
      (fst (bousfieldKanWeight I) ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ φ))))

/-- 指定 BK 入力から得る、同じ頂点を持つ実際の join 錐。 -/
def reflectedWeightedNativeCone : JoinCone (strictCoherentDiagram F) :=
  ((fixedVertexConeSpaceEquiv (strictCoherentDiagram F) (coherentNerveVertex x)).symm
    (reflectedWeightedConeSectionPoint F x φ)).val

/-- 左端は指定された元の頂点そのものである。 -/
theorem reflectedWeightedNativeCone_vertexMap :
    joinInl (Δ[0] : SSet.{max u v}) _ ≫ (reflectedWeightedNativeCone F x φ).val =
      SSet.yonedaEquiv.symm (coherentNerveVertex x) :=
  ((fixedVertexConeSpaceEquiv (strictCoherentDiagram F) (coherentNerveVertex x)).symm
    (reflectedWeightedConeSectionPoint F x φ)).property

/-- 錐を切断へ戻すと、指定比較で作った同じ点に戻る。 -/
theorem reflectedWeightedNativeCone_section :
    fixedVertexConeSpaceEquiv (strictCoherentDiagram F) (coherentNerveVertex x)
      ⟨reflectedWeightedNativeCone F x φ, reflectedWeightedNativeCone_vertexMap F x φ⟩ =
        reflectedWeightedConeSectionPoint F x φ :=
  (fixedVertexConeSpaceEquiv (strictCoherentDiagram F) (coherentNerveVertex x)).apply_symm_apply _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
