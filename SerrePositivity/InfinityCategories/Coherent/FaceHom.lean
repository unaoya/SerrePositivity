module

public import SerrePositivity.InfinityCategories.Coherent.FaceRetraction
public import SerrePositivity.InfinityCategories.Coherent.HornData

/-!
# 既知面からの Hom 写像の候補

概要：coherent nerve のホーンの面から Hom 写像を回収する道具を構成する。
方針：面と退化の順序写像、Path の関手性、共通の端点への型の移送を使う。
規約：面候補の全体の貼合せとホーン充填は後続工程で証明する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8–2.4.5.10。
-/

@[expose] public section

universe w v u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Coherent

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]
/-- 概要：既知面を退化で引き戻し、共通の対象の間の Hom 写像の候補を作る。
方針：Path の退化関手、面の Hom 写像、端点比較を合成する。
規約：単体の面 δ の除外頂点を j とし、ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8 の零座標面からの Hom データの貼合せ。 -/
def hornHomViaFace {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (a b : Fin (n + 3)) (ha : a ≠ j) (hb : b ≠ j) :
    nerve (SimplicialThickening.Path (ULift.up.{v} a) (ULift.up.{v} b)) ⟶
      SimplicialCategory.sHom (hornObj σ a) (hornObj σ b) :=
  (SimplicialThickening.functor (faceRetraction j).toOrderHom.uliftMap).map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ≫
    hornHomOnCell σ (SSet.horn.face i j hj) ((faceRetraction j).toOrderHom a)
      ((faceRetraction j).toOrderHom b) ≫ eqToHom (by
        change SimplicialCategory.sHom
          (hornObj σ (j.succAbove ((faceRetraction j).toOrderHom a)))
          (hornObj σ (j.succAbove ((faceRetraction j).toOrderHom b))) = _
        rw [faceRetraction_point j a ha, faceRetraction_point j b hb])
set_option backward.isDefEq.respectTransparency false in
/-- 概要：面から作った Hom 候補は移送前の豊穣写像の合成と異種等号で一致する。
方針：二段の型の移送を消去する。
規約：単体の面 δ の除外頂点を j とし、ULift の宇宙を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8 の零座標面からの Hom データの貼合せ。 -/
lemma hornHomViaFace_heq {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (a b : Fin (n + 3)) (ha : a ≠ j) (hb : b ≠ j) :
    HEq (hornHomViaFace σ j hj a b ha hb)
      ((SimplicialThickening.functor (faceRetraction j).toOrderHom.uliftMap).map
        ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ≫
        (σ.app _ (SSet.horn.face i j hj)).map
          ⟨⟨(faceRetraction j).toOrderHom a⟩⟩ ⟨⟨(faceRetraction j).toOrderHom b⟩⟩) := by
  simp only [hornHomViaFace, hornHomOnCell, ← Category.assoc, comp_eqToHom_heq_iff]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- 概要：既知面からの Hom 候補をその面へ制限すると元の Hom 写像に戻る。
方針：面と退化の合成が恒等射であることを nerve の関手性へ移し、型の移送を消去する。
規約：面への埋め込みを合成した厳密な写像の等式。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8 の零座標面の貼合せ。
他の面との重なりや合成面との整合性は後続工程で扱う。 -/
lemma hornHomViaFace_on_face {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (a b : Fin (n + 2)) :
    (SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map
      ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ≫
      hornHomViaFace σ j hj (j.succAbove a) (j.succAbove b)
        (Fin.succAbove_ne j a) (Fin.succAbove_ne j b) =
        hornHomOnCell σ (SSet.horn.face i j hj) a b := by
  apply eq_of_heq
  simp only [hornHomViaFace, hornHomOnCell, ← Category.assoc,
    comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
  let F := σ.app _ (SSet.horn.face i j hj)
  have hF : (SimplicialNerve C).map (SimplexCategory.δ j).op
      ((SimplicialNerve C).map (faceRetraction j).op F) = F := by
    rw [← CategoryTheory.Functor.map_comp_apply, ← op_comp, faceRetraction_section,
      op_id, CategoryTheory.Functor.map_id]
    rfl
  have hmap (F G : EnrichedFunctor SSet
      (SimplicialThickening (ULift.{v} (Fin (n + 2)))) C) (h : F = G) :
      HEq (F.map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩) (G.map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩) := by
    subst G
    rfl
  exact hmap _ _ hF

end SerrePositivity.InfinityCategories.Coherent
