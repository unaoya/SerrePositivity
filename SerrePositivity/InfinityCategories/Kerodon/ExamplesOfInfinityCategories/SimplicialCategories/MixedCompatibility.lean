module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FaceIntervalRestriction
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathMixedFaces
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionRecovery

/-!
# 零座標面と合成面上の回収写像の一致

概要：零座標面と合成面の交わり全体で両方の回収写像が一致することを証明する。
方針：面内 Hom の直積で前合成し、標準回収の面への制限と元の豊穣関手の合成則を使う。
規約：両脚の真部分性だけを仮定し、外側区間の真部分性は不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の空洞部分への貼合せ。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- 概要：既知面の零座標面と合成面の交わり上で、面候補と合成面の回収は厳密に一致する。
方針：pathMixedFaceIso で前合成し、両脚の標準回収を元の面の回収へ戻して合成則を適用する。
規約：端点と切断点を同じ既知面の頂点の像で表す。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.9（Tag 00LS） の混合した重なりの整合性。 -/
lemma hornCompositionHom_zero_overlap {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (j : Fin (n + 3)) (hj : j ≠ i)
    (a b c : Fin (n + 2)) (hab : a ≤ b) (hbc : b ≤ c)
    (hpab : j.succAbove a ≠ 0 ∨ j.succAbove b ≠ Fin.last (n + 2))
    (hpbc : j.succAbove b ≠ 0 ∨ j.succAbove c ≠ Fin.last (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{v} (j.succAbove a)) (b := ULift.up (j.succAbove c))
      (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (j.succAbove b))).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj (j.succAbove a) (j.succAbove c)
        (Fin.succAbove_ne j a) (Fin.succAbove_ne j c) =
    SSet.Subcomplex.homOfLE
      (show (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{v} (j.succAbove a))
        (b := ULift.up (j.succAbove c)) (ULift.up j) ⊓
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (j.succAbove b))) ≤
            _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (j.succAbove b)) from inf_le_right) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornCompositionHom σ h0 hn (j.succAbove a) (j.succAbove b) (j.succAbove c)
        ((Fin.strictMono_succAbove j).monotone hab)
        ((Fin.strictMono_succAbove j).monotone hbc) hpab hpbc := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathMixedFaceIso.{v} j a b c).hom).mp
  simp only [← Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathMixedFaceIso_hom_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathMixedFaceIso_hom_toThrough]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornCompositionHom_on_product]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceCompositionMap_eq_native, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace_on_face]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom_on_face σ h0 hn j hj a b hab hpab,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom_on_face σ h0 hn j hj b c hbc hpbc]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell_comp σ (SSet.horn.face i j hj) a b c

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
