module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.FaceIntervals

/-!
# 後ろの面と拡張退化の交換

概要：指定面より後ろの面と拡張退化を交換する。
方針：和を保つ写像を singleton 上で比較し、追加する初期区間の像を照合する。
規約：Moss 2020 Lemma 26 (3)。
使われ方：pairing の対応先の後ろの面が再び拡張の像となること。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory PartialOrder

/--
概要：後ろの面の像の特別な頂点は元の特別な頂点である。
方針：添字の不等式から、面写像がその頂点をずらさないことを使う。
規約：Moss 2020 Lemma 26 (3) の特別な場合。
使われ方：拡張退化の通常の退化と異なる頂点の照合。
-/
theorem liftedFace_special (n : ℕ) (k : Fin (n + 1)) (j : Fin (n + 2))
    (hkj : k.castSucc < j) :
    liftedFace.{u} (n + 1) j.succ (ULift.up k.succ) = ULift.up k.castSucc.succ := by
  apply ULift.ext
  change j.succ.succAbove k.succ = k.castSucc.succ
  calc
    _ = k.succ.castSucc :=
      Fin.succAbove_succ_of_le j k.succ (Fin.castSucc_lt_iff_succ_le.mp hkj)
    _ = _ := Fin.ext rfl

/--
概要：後ろの面と有限鎖の拡張退化は交換する。
方針：singleton 上で特別な頂点を分け、残りは通常の面・退化の恒等式を使う。
規約：Moss 2020 Lemma 26 (3)、原典の面の添字は j+1。
使われ方：対応先の後ろの面の表示。
-/
theorem finiteChainDegeneracy_face_right (n : ℕ) (k : Fin (n + 1)) (j : Fin (n + 2))
    (hkj : k.castSucc < j) :
    (finiteChainDegeneracy.{u} (n + 1) k.castSucc ∘ fun s => s.map (liftedFace (n + 1) j.succ)) =
      ((fun s => s.map (liftedFace n j)) ∘ finiteChainDegeneracy n k) := by
  apply finiteChainUnion_ext
    ((finiteChainDegeneracy_preservesUnion (n + 1) k.castSucc).comp
      (finiteChainMap_preservesUnion (liftedFace (n + 1) j.succ)))
    ((finiteChainMap_preservesUnion (liftedFace n j)).comp
      (finiteChainDegeneracy_preservesUnion n k))
  intro i
  change finiteChainDegeneracy (n + 1) k.castSucc
      ((finiteChainSingleton i).map (liftedFace (n + 1) j.succ)) =
    (finiteChainDegeneracy n k (finiteChainSingleton i)).map (liftedFace n j)
  rw [finiteChainMap_singleton, finiteChainDegeneracy_singleton, finiteChainDegeneracy_singleton]
  by_cases hi : i = ULift.up k.succ
  · rw [ite_eq_left hi]
    subst i
    rw [liftedFace_special n k j hkj, ite_eq_left rfl,
      liftedFace_initialSegment_of_below n j k hkj]
  · rw [ite_eq_right hi]
    have hn : liftedFace (n + 1) j.succ i ≠ ULift.up k.castSucc.succ := by
      intro h
      apply hi
      apply liftedFace_injective (n + 1) j.succ
      exact h.trans (liftedFace_special n k j hkj).symm
    rw [ite_eq_right hn, finiteChainMap_singleton]
    apply congrArg finiteChainSingleton
    apply ULift.ext
    exact congrArg
      (fun f : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk (n + 1) => f i.down)
      (SimplexCategory.δ_comp_σ_of_gt (i := j) (j := k) hkj)

/--
概要：細分の後ろの面と拡張退化の交換則。
方針：有限鎖上の式を nerve の各頂点で使う。
規約：Moss 2020 Lemma 26 (3)、原典の i はこの宣言の j+1。
使われ方：pairing の指定面以外の後ろの面の複雑度。
-/
@[reassoc] theorem subdivisionDegeneracyAt_face_right (n : ℕ) (k : Fin (n + 1))
    (j : Fin (n + 2)) (hkj : k.castSucc < j) :
    SimplexCategory.sd.map (SimplexCategory.δ j.succ) ≫
      subdivisionDegeneracyAt.{u} (n + 1) k.castSucc =
      subdivisionDegeneracyAt n k ≫ SimplexCategory.sd.map (SimplexCategory.δ j) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  exact congrFun (finiteChainDegeneracy_face_right n k j hkj) (s.obj i)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
