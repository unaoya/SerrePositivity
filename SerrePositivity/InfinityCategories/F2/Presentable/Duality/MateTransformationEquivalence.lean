module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairAdjointCondition
public import SerrePositivity.InfinityCategories.HomotopyLimits.PostcompositionAdjunction
public import SerrePositivity.InfinityCategories.F1B.Adjunction.AdjunctionPinchedSpaces

/-!
概要：固定した二つの随伴の間の全自然変換空間の反変同値。
方針：後合成随伴と前合成随伴の区間 Hom 同値を、同じ中間空間で接続する。
規約：非可逆な自然変換を含み、全関手圏の同値自体は別工程で構成する。
使われ方：対ごとの双対性の充満忠実性の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：左関手間の全自然変換空間と、逆向きの右関手間の全自然変換空間の同値。
方針：両方を id→L₂R₁ の同じ区間 Hom 空間に比較する。
規約：元の関手と全高次の変換を保持し、全関手圏同値の存在は仮定しない。
使われ方：対ごとの反変同値の写像空間比較。 -/
def adjointTransformationEquivalence {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D]
    {L₁ L₂ : C ⟶ D} {R₁ R₂ : D ⟶ C}
    (a₁ : QCatAdjunction L₁ R₁) (a₂ : QCatAdjunction L₂ R₂) :
    QCatEquivalence
      (intervalMappingSpace (functorVertex L₁) (functorVertex L₂))
      (intervalMappingSpace (functorVertex R₂) (functorVertex R₁)) := by
  have e₁ := (HomotopyLimits.postcompositionAdjunction a₁ C).intervalMappingEquivalence
    (functorVertex (𝟙 C)) (functorVertex L₂)
  have h₁ : ((ihom C).map L₁).app (Opposite.op ⦋0⦌) (functorVertex (𝟙 C)) =
      functorVertex L₁ := by
    change functorVertex (𝟙 C ≫ L₁) = _
    rw [Category.id_comp]
  rw [h₁] at e₁
  have e₂ := (precompositionAdjunction (Z := C) a₂).intervalMappingEquivalence
    (functorVertex (𝟙 C)) (functorVertex R₁)
  have h₂ : ((pre R₂).app C).app (Opposite.op ⦋0⦌) (functorVertex (𝟙 C)) =
      functorVertex R₂ := by
    change functorVertex (R₂ ≫ 𝟙 C) = _
    rw [Category.comp_id]
  rw [h₂] at e₂
  exact e₁.trans e₂.symm

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
