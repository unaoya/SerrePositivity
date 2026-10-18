module

public import SerrePositivity.InfinityCategories.Coherent.FaceIntervalRestriction
public import SerrePositivity.InfinityCategories.Coherent.PathMixedFaces
public import SerrePositivity.InfinityCategories.Coherent.CompositionRecovery

/-!
# 零座標面と合成面上の回収写像の一致

概要：零座標面と合成面の交わり全体で両方の回収写像が一致することを証明する。
方針：面内 Hom の直積で前合成し、標準回収の面への制限と元の豊穣関手の合成則を使う。
規約：両脚の真部分性だけを仮定し、外側区間の真部分性は不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8–2.4.5.9 の空洞部分への貼合せ。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Coherent

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- 概要：既知面の零座標面と合成面の交わり上で、面候補と合成面の回収は厳密に一致する。
方針：pathMixedFaceIso で前合成し、両脚の標準回収を元の面の回収へ戻して合成則を適用する。
規約：端点と切断点を同じ既知面の頂点の像で表す。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8–2.4.5.9 の混合した重なりの整合性。 -/
lemma hornCompositionHom_zero_overlap {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (j : Fin (n + 3)) (hj : j ≠ i)
    (a b c : Fin (n + 2)) (hab : a ≤ b) (hbc : b ≤ c)
    (hpab : j.succAbove a ≠ 0 ∨ j.succAbove b ≠ Fin.last (n + 2))
    (hpbc : j.succAbove b ≠ 0 ∨ j.succAbove c ≠ Fin.last (n + 2)) :
    (pathAvoids (a := ULift.up.{v} (j.succAbove a)) (b := ULift.up (j.succAbove c))
      (ULift.up j) ⊓ pathThrough (ULift.up (j.succAbove b))).ι ≫
      hornHomViaFace σ j hj (j.succAbove a) (j.succAbove c)
        (Fin.succAbove_ne j a) (Fin.succAbove_ne j c) =
    SSet.Subcomplex.homOfLE
      (show (pathAvoids (a := ULift.up.{v} (j.succAbove a))
        (b := ULift.up (j.succAbove c)) (ULift.up j) ⊓
          pathThrough (ULift.up (j.succAbove b))) ≤
            pathThrough (ULift.up (j.succAbove b)) from inf_le_right) ≫
      hornCompositionHom σ h0 hn (j.succAbove a) (j.succAbove b) (j.succAbove c)
        ((Fin.strictMono_succAbove j).monotone hab)
        ((Fin.strictMono_succAbove j).monotone hbc) hpab hpbc := by
  apply (cancel_epi (pathMixedFaceIso.{v} j a b c).hom).mp
  simp only [← Category.assoc]
  rw [pathMixedFaceIso_hom_ι, pathMixedFaceIso_hom_toThrough]
  rw [Category.assoc, hornCompositionHom_on_product]
  rw [pathFaceCompositionMap_eq_native, Category.assoc, pathFaceMap, hornHomViaFace_on_face]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  simp only [pathFaceMap]
  rw [hornProperIntervalHom_on_face σ h0 hn j hj a b hab hpab,
    hornProperIntervalHom_on_face σ h0 hn j hj b c hbc hpbc]
  exact hornHomOnCell_comp σ (SSet.horn.face i j hj) a b c

end SerrePositivity.InfinityCategories.Coherent
