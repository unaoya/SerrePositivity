module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SimplicialSections

/-!
概要：Bousfield–Kan 重み付き end と weighted nerve の切断空間の同型。
方針：切断の族との自然な全単射を普遍的な評価に適用し、両逆関係を一意性で示す。
規約：任意の単体集合値図式を扱い、Kan 性や fibration 性は要求しない。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の homotopy 極限の切断模型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {I : Type u} [SmallCategory I]

/-- 概要：Bousfield–Kan 重み付き end から weighted nerve の切断空間への標準射。
方針：普遍的な weighted nerve の切断の族を切断空間へ持ち上げる。
規約：定義は局所 Kan 性や極限性を要求しない。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の end から切断模型への比較。 -/
noncomputable def bousfieldKanSectionsMap (H : I ⥤ SSet.{u}) :
    bousfieldKanHolim H ⟶ simplicialSections (weightedNerveProjection H) :=
  simplicialSectionsLift (bousfieldKanWeightedNerveEvaluation H)
    (bousfieldKanWeightedNerveEvaluation_projection H)

/-- 概要：end から切断空間への標準射を評価すると普遍的な weighted nerve の切断の族になる。
方針：切断空間への持ち上げの評価の公式を使う。
規約：底を保つ実際の射の等式。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の標準比較の評価式。 -/
lemma bousfieldKanSectionsMap_evaluation (H : I ⥤ SSet.{u}) :
    (nerve I ◁ bousfieldKanSectionsMap H) ≫
      simplicialSectionsEvaluation (weightedNerveProjection H) =
        bousfieldKanWeightedNerveEvaluation H :=
  simplicialSectionsLift_evaluation _ _

/-- 概要：weighted nerve の切断空間から Bousfield–Kan 重み付き end への逆射。
方針：普遍的な切断の族を重み付き自然変換へ戻し、end の普遍性で束ねる。
規約：任意の図式で定義する。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の切断模型から end への比較。 -/
noncomputable def sectionsBousfieldKanMap (H : I ⥤ SSet.{u}) :
    simplicialSections (weightedNerveProjection H) ⟶ bousfieldKanHolim H :=
  (bousfieldKanSectionHomEquiv H (simplicialSections (weightedNerveProjection H))).symm
    ⟨simplicialSectionsEvaluation (weightedNerveProjection H),
      simplicialSectionsEvaluation_projection (weightedNerveProjection H)⟩

/-- 概要：切断空間から end への逆射の評価は普遍的な切断の族に一致する。
方針：切断の族との全単射の右逆関係と普遍的な評価式を使う。
規約：厳密な射の等式として述べる。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の比較射の逆性。 -/
lemma sectionsBousfieldKanMap_evaluation (H : I ⥤ SSet.{u}) :
    (nerve I ◁ sectionsBousfieldKanMap H) ≫ bousfieldKanWeightedNerveEvaluation H =
      simplicialSectionsEvaluation (weightedNerveProjection H) := by
  have he := congrArg Subtype.val ((bousfieldKanSectionHomEquiv H
    (simplicialSections (weightedNerveProjection H))).apply_symm_apply
      ⟨simplicialSectionsEvaluation (weightedNerveProjection H),
        simplicialSectionsEvaluation_projection (weightedNerveProjection H)⟩)
  rw [bousfieldKanSectionHomEquiv_apply] at he
  exact he

/-- 概要：end から切断空間を経て戻す合成は恒等射である。
方針：切断の族との全単射で射を比較し、二つの評価の等式を使う。
規約：ホモトピー同値に弱めず厳密な逆関係を示す。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の end 側の逆関係。 -/
lemma bousfieldKanSectionsMap_reverse (H : I ⥤ SSet.{u}) :
    bousfieldKanSectionsMap H ≫ sectionsBousfieldKanMap H = 𝟙 (bousfieldKanHolim H) := by
  apply (bousfieldKanSectionHomEquiv H (bousfieldKanHolim H)).injective
  apply Subtype.ext
  rw [bousfieldKanSectionHomEquiv_apply, bousfieldKanSectionHomEquiv_apply,
    whiskerLeft_comp, Category.assoc, sectionsBousfieldKanMap_evaluation,
    bousfieldKanSectionsMap_evaluation, whiskerLeft_id, Category.id_comp]

/-- 概要：切断空間から end を経て戻す合成は恒等射である。
方針：普遍的な切断の族で評価して射を比較する。
規約：全ての図式で厳密に成立する。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の切断空間側の逆関係。 -/
lemma sectionsBousfieldKanMap_reverse (H : I ⥤ SSet.{u}) :
    sectionsBousfieldKanMap H ≫ bousfieldKanSectionsMap H =
      𝟙 (simplicialSections (weightedNerveProjection H)) := by
  apply simplicialSections_hom_ext
  rw [whiskerLeft_comp, Category.assoc, bousfieldKanSectionsMap_evaluation,
    sectionsBousfieldKanMap_evaluation, whiskerLeft_id, Category.id_comp]

/-- 概要：Bousfield–Kan 重み付き end は weighted nerve の切断空間と厳密に同型である。
方針：両向きの普遍的な評価から作った射とその両逆関係を組み合わせる。
規約：図式の値の Kan 性も添字の有限性も要求しない。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の極限の切断模型への比較。 -/
noncomputable def bousfieldKanSectionsIso (H : I ⥤ SSet.{u}) :
    bousfieldKanHolim H ≅ simplicialSections (weightedNerveProjection H) where
  hom := bousfieldKanSectionsMap H
  inv := sectionsBousfieldKanMap H
  hom_inv_id := bousfieldKanSectionsMap_reverse H
  inv_hom_id := sectionsBousfieldKanMap_reverse H

end SerrePositivity.InfinityCategories.HomotopyLimits
