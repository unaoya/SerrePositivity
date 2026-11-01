module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordPaddedCollapse
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordEmbeddingUniqueness
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordCut

/-!
# 三列の二つの元の padding 包含と切断位置

概要：中央の forward 列の包含と両端 padding による二つの三列の写像を定める。
方針：元の語の射として構成し、全列と全頂点の有限表を検証する。
規約：外側は B の写像、内側は元の paddingInclusionNat の成分である。
使われ方：元の WordAction と明示的な二つの恒等列配置の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ThreeArrow.Padding
open CategoryTheory

def centerInclusion : Word.single .forward ⟶ Word.threeArrow where
  orderHom := OrderHom.const _ (1 : Fin 3)
  direction_eq _ := rfl

def outerWordMap : Word.threeArrow ⟶ Word.paddingFunctor.obj Word.threeArrow :=
  eqToHom Word.padding_single_forward.symm ≫ Word.paddingFunctor.map centerInclusion

def innerWordMap : Word.threeArrow ⟶ Word.paddingFunctor.obj Word.threeArrow :=
  Word.paddingInclusionNat.app Word.threeArrow

lemma outerWordMap_columns :
    (fun i : Fin 3 => outerWordMap.orderHom i) = (![0, 2, 4] : Fin 3 → Fin 5) := by
  funext i
  change (Word.paddingFunctor.map centerInclusion).orderHom
    ((eqToHom Word.padding_single_forward.symm).orderHom i) = _
  rw [Word.eqToHom_apply]
  fin_cases i <;> rfl

lemma innerWordMap_columns :
    (fun i : Fin 3 => innerWordMap.orderHom i) = (![1, 2, 3] : Fin 3 → Fin 5) := by
  funext i
  fin_cases i <;> rfl

lemma outerWordMap_cut :
    (fun j : Fin 6 => outerWordMap.cut j) = (![0, 1, 1, 2, 2, 3] : Fin 6 → Fin 4) := by
  funext j
  apply Word.Hom.vertex_ext
  intro i
  rw [Word.Hom.lt_cut_iff]
  change (outerWordMap.orderHom i).val < j.val ↔ _
  rw [congrFun outerWordMap_columns i]
  fin_cases i <;> fin_cases j <;> decide

lemma innerWordMap_cut :
    (fun j : Fin 6 => innerWordMap.cut j) = (![0, 0, 1, 2, 3, 3] : Fin 6 → Fin 4) := by
  funext j
  apply Word.Hom.vertex_ext
  intro i
  rw [Word.Hom.lt_cut_iff]
  change (innerWordMap.orderHom i).val < j.val ↔ _
  rw [congrFun innerWordMap_columns i]
  fin_cases i <;> fin_cases j <;> decide

end SerrePositivity.EInfinity.Hammock.ThreeArrow.Padding
