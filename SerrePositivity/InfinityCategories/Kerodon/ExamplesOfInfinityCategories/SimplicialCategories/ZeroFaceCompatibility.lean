module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FaceCellCompatibility
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathFaceIntersections

/-!
# 零座標面の交わり全体での Hom 写像の一致

概要：二つの零座標面の交わり上で、両面からの Hom 候補は厳密に一致する。
方針：交わりと共通面の Hom の同型で前合成し、共通単体上の一致へ戻す。
規約：端点は二つの除外点を避ける共通面の頂点で書く。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面の貼合せ。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- 概要：二つの零座標面の交わりに制限した Hom 候補は一致する。
方針：pathDoubleFaceIso に沿って比較し、二点を避ける共通単体上の一致を適用する。
規約：除外する点は j と j.succAbove k、どちらの面もホーンに含まれる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面の重なりの整合性。 -/
lemma hornHomViaFace_zero_overlap {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (k : Fin (n + 2)) (hj : j ≠ i) (hk : j.succAbove k ≠ i)
    (a b : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{v} (j.succAbove (k.succAbove a)))
      (b := ULift.up (j.succAbove (k.succAbove b))) (ULift.up j) ⊓
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up (j.succAbove k))).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj (j.succAbove (k.succAbove a))
        (j.succAbove (k.succAbove b)) (Fin.succAbove_ne j _) (Fin.succAbove_ne j _) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{v} (j.succAbove (k.succAbove a)))
      (b := ULift.up (j.succAbove (k.succAbove b))) (ULift.up j) ⊓
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up (j.succAbove k))).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ (j.succAbove k) hk (j.succAbove (k.succAbove a))
        (j.succAbove (k.succAbove b))
        (fun h ↦ Fin.succAbove_ne k a ((Fin.strictMono_succAbove j).injective h))
        (fun h ↦ Fin.succAbove_ne k b ((Fin.strictMono_succAbove j).injective h)) := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathDoubleFaceIso.{v} j k a b).hom).mp
  simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathDoubleFaceIso_hom_ι]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathDoubleFaceMap_eq_native]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace_common_cell σ (SimplexCategory.δ k ≫ SimplexCategory.δ j)
    j (j.succAbove k) hj hk (fun t ↦ Fin.succAbove_ne j (k.succAbove t))
    (fun t h ↦ Fin.succAbove_ne k t ((Fin.strictMono_succAbove j).injective h)) a b

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
