module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TransportSectionsCone

/-!
概要：元の切断を under 圏へ制限して組み立て直す操作の逆関係。
方針：標準の under 圏の射列を忘れると元の射列になることを使う。
規約：単体集合の射の厳密な等式を証明する。
使われ方：Kerodon 5.3.4.7（Tag 026D）、7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の strict transport の切断の復元。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
variable {I : Type u} [SmallCategory I] {E : SSet.{u}}

/-- 概要：切断の制限から作った strict transport の錐を組み立てると普遍的な切断の族になる。
方針：scaffold の対角評価を展開し、標準 under 射列の忘却と直積の評価を計算する。
規約：元の射影の left fibration 性は不要。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の切断側の復元の逆関係。 -/
lemma strictTransportConeAssembly_sections (p : E ⟶ nerve I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportConeAssembly p (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsCone p) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, a⟩
  let b : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p := SSet.yonedaEquiv.symm a
  let w : (Δ[n] : SSet.{u}) ⟶ nerve (Under (σ.obj 0)) :=
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain σ)
  have he : lift w (𝟙 (Δ[n] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsRestriction p (σ.obj 0)) =
        lift (SSet.yonedaEquiv.symm σ) b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.relativeFunctorUncurry_parameter, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsRestriction_evaluation]
    simp only [← Category.assoc]
    rw [lift_whiskerLeft, Category.id_comp, lift_whiskerRight]
    have hw : w ≫ nerveMap (Under.forget (σ.obj 0)) = SSet.yonedaEquiv.symm σ :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain_yoneda_projection σ
    rw [hw]
  change SSet.yonedaEquiv (lift w (𝟙 (Δ[n] : SSet.{u})) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsRestriction p (σ.obj 0))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p).app (Opposite.op ⦋n⦌) (σ, a)
  rw [he, SSet.yonedaEquiv_comp]
  congr 1
  apply Prod.ext
  · change (fst (nerve I) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p)).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (lift (SSet.yonedaEquiv.symm σ) b)) = σ
    rw [← SSet.yonedaEquiv_comp, lift_fst, Equiv.apply_symm_apply]
  · change (snd (nerve I) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p)).app (Opposite.op ⦋n⦌)
      (SSet.yonedaEquiv (lift (SSet.yonedaEquiv.symm σ) b)) = a
    rw [← SSet.yonedaEquiv_comp, lift_snd]
    exact SSet.yonedaEquiv.apply_symm_apply a

/-- 概要：切断空間を strict transport の錐へ写して戻すと恒等射になる。
方針：切断空間の評価の一意性と組み立ての評価の等式を使う。
規約：元の射影の充填性や添字圏の形は任意。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の strict transport の極限比較の切断側の逆関係。 -/
lemma strictTransportConeSections_sections (p : E ⟶ nerve I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportConeSections p (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.transportSectionsCone p) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportConeSections, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift_evaluation,
    strictTransportConeAssembly_sections]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p =
    (nerve I ◁ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections p)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation p
  rw [whiskerLeft_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
