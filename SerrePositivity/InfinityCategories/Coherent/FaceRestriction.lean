module

public import SerrePositivity.InfinityCategories.Coherent.PathFaces
public import SerrePositivity.InfinityCategories.Coherent.FaceHom

/-!
# ホーンの零座標面上の Hom 写像

概要：実際の零座標面を定義域とする Hom 写像を構成し、面からの候補の制限と比較する。
方針：Path の面の像との同型を使い、元の面の豊穣関手を評価する。
規約：異なる零座標面の重なりでの一致は後続工程。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8 の空洞部分への貼合せ。
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.SimplicialThickening
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Coherent

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- 概要：ホーンの既知面から、除外頂点を避ける Path の零座標面上の Hom 写像を作る。
方針：零座標面の同型を逆にたどり、既知面の Hom 写像を適用する。
規約：端点は既知面の頂点 a,b の像。局所 Kan 性は不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8 の面からの既知データの回収。 -/
noncomputable def hornZeroFaceHom {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (a b : Fin (n + 2)) :
    (pathAvoids (a := ULift.up.{v} (j.succAbove a))
      (b := ULift.up (j.succAbove b)) (ULift.up j) : SSet) ⟶
      SimplicialCategory.sHom (hornObj σ (j.succAbove a)) (hornObj σ (j.succAbove b)) :=
  (pathFaceIso j a b).inv ≫ hornHomOnCell σ (SSet.horn.face i j hj) a b

set_option backward.isDefEq.respectTransparency false in
/-- 概要：面からの Hom 候補を零座標面へ制限すると零座標面の Hom 写像に等しい。
方針：Path の面の同型で前合成し、既知面への制限一致を適用する。
規約：候補を定義域全体で選んだことはこの制限等式を変更しない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8 の零座標面の貼合せ。 -/
lemma hornHomViaFace_restrict {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (a b : Fin (n + 2)) :
    (pathAvoids (a := ULift.up.{v} (j.succAbove a))
      (b := ULift.up (j.succAbove b)) (ULift.up j)).ι ≫
      hornHomViaFace σ j hj (j.succAbove a) (j.succAbove b)
        (Fin.succAbove_ne j a) (Fin.succAbove_ne j b) = hornZeroFaceHom σ j hj a b := by
  apply (cancel_epi (pathFaceIso.{v} j a b).hom).mp
  calc
    _ = pathFaceMap.{v} j a b ≫
        hornHomViaFace σ j hj (j.succAbove a) (j.succAbove b)
          (Fin.succAbove_ne j a) (Fin.succAbove_ne j b) := by
      rw [← Category.assoc, pathFaceIso_hom_ι]
    _ = hornHomOnCell σ (SSet.horn.face i j hj) a b :=
      hornHomViaFace_on_face σ j hj a b
    _ = _ := by simp [hornZeroFaceHom]

end SerrePositivity.InfinityCategories.Coherent
