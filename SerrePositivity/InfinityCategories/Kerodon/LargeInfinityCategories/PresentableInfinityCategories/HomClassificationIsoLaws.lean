module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomClassificationLaws

/-!
概要：分類した同じ底上の同型と逆射の合成は恒等射。
方針：元の分類の合成則・恒等則と、元の同型の逆射の法則だけを使う。
規約：元の同型と両三角形を保持する。
使われ方：Kerodon §5.6（Tag 027M）の標準反復引き戻し比較の分類後の相殺。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
namespace PresentableInfinityCategories

/-- 概要：同じ底上の同型の順方向・逆方向の分類の合成は恒等。
方針：分類の合成則と恒等則を使う。規約：元の射。使われ方：補正因子の消去。 -/
lemma leftClassificationHom_iso_hom_inv {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (e : E ≅ H) (he : e.hom ≫ q = p) (hi : e.inv ≫ p = q) :
    leftClassificationHom p q e.hom he ≫ leftClassificationHom q p e.inv hi = 𝟙 _ := by
  rw [leftClassificationHom_comp]
  simpa only [Iso.hom_inv_id] using leftClassificationHom_id p

/-- 概要：同じ底上の同型の逆方向・順方向の分類の合成も恒等。
方針：分類の合成則と恒等則を使う。規約：元の逆射。使われ方：補正因子の消去。 -/
lemma leftClassificationHom_iso_inv_hom {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (e : E ≅ H) (he : e.hom ≫ q = p) (hi : e.inv ≫ p = q) :
    leftClassificationHom q p e.inv hi ≫ leftClassificationHom p q e.hom he = 𝟙 _ := by
  rw [leftClassificationHom_comp]
  simpa only [Iso.inv_hom_id] using leftClassificationHom_id q

end PresentableInfinityCategories
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
