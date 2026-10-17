module
public import SerrePositivity.InfinityCategories.DGNerve.JoinSimplexFaces

/-! # cospan と標準単体の join の二つのセル

概要：任意次元の cospan の錐を二つの標準単体の pushout として表示する。
方針：右因子のホーンの pushout を標準 join 同型で移送する。
規約：HTT §1.2.8・§1.2.13。使われ方：N7c の slice 境界を二つの単体として充填する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Limits
open scoped Simplicial

/-- 概要：cospan の左の辺との join の標準セル。
方針：標準 join 同型の逆の後に左の辺の join を合成する。
規約：HTT §1.2.13、末尾の二頂点は B,D。使われ方：左の単体の成分。 -/
def cospanJoinLeft (n : ℕ) : (Δ[n + 2] : SSet.{u}) ⟶ join Δ[n] (SSet.horn 2 2) :=
  (joinStdSimplexIso n 1).inv ≫ joinMap (𝟙 Δ[n]) SSet.horn₂₂.ι₀₂

/-- 概要：cospan の右の辺との join の標準セル。
方針：標準 join 同型の逆の後に右の辺の join を合成する。
規約：HTT §1.2.13、末尾の二頂点は C,D。使われ方：右の単体の成分。 -/
def cospanJoinRight (n : ℕ) : (Δ[n + 2] : SSet.{u}) ⟶ join Δ[n] (SSet.horn 2 2) :=
  (joinStdSimplexIso n 1).inv ≫ joinMap (𝟙 Δ[n]) SSet.horn₂₂.ι₁₂

/-- 概要：cospan の join は二つの標準セルを D 側の共通面で貼る pushout。
方針：ホーンの join の pushout を標準単体との同型で移送する。
規約：HTT §1.2.13、共通面は番号 n+1。使われ方：充填後の二単体を一つの slice 単体へ貼る。 -/
lemma cospanJoin_isPushout (n : ℕ) :
    IsPushout (SSet.stdSimplex.δ ((Fin.last (n + 1)).castSucc))
      (SSet.stdSimplex.δ ((Fin.last (n + 1)).castSucc))
      (cospanJoinLeft.{u} n) (cospanJoinRight n) := by
  apply (joinRight_horn₂₂_isPushout (Δ[n] : SSet.{u})).of_iso'
    (joinStdSimplexIso n 0).symm (joinStdSimplexIso n 1).symm
    (joinStdSimplexIso n 1).symm (Iso.refl _)
  · apply (cancel_mono (joinStdSimplexIso n 1).hom).1
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [joinStdSimplexIso_right_last, Iso.inv_hom_id_assoc]
  · apply (cancel_mono (joinStdSimplexIso n 1).hom).1
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [joinStdSimplexIso_right_last, Iso.inv_hom_id_assoc]
  · rfl
  · rfl

/-- 概要：左セルの先頭の面は可変因子の同じ面の左セル。
方針：標準 join の左面の公式と joinMap の合成則を使う。
規約：HTT §1.2.8・§1.2.13。使われ方：slice 境界に一致する左単体の面の指定。 -/
lemma cospanJoinLeft_face (n : ℕ) (j : Fin (n + 2)) :
    SSet.stdSimplex.δ (j.castAdd 2) ≫ cospanJoinLeft.{u} (n + 1) =
      cospanJoinLeft n ≫ joinMap (SSet.stdSimplex.δ j) (𝟙 (SSet.horn 2 2 : SSet.{u})) := by
  have h := joinStdSimplexIso_left_face.{u} n j
  have hi : SSet.stdSimplex.δ (j.castAdd 2) ≫ (joinStdSimplexIso (n + 1) 1).inv =
      (joinStdSimplexIso n 1).inv ≫ joinMap (SSet.stdSimplex.δ j) (𝟙 Δ[1]) := by
    apply (cancel_mono (joinStdSimplexIso (n + 1) 1).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h, Iso.inv_hom_id_assoc]
  simp only [cospanJoinLeft, ← Category.assoc]
  rw [hi]
  simp only [Category.assoc]
  congr 1
  rw [← joinMap_comp, ← joinMap_comp]
  simp only [Category.id_comp, Category.comp_id]

/-- 概要：右セルの先頭の面は可変因子の同じ面の右セル。
方針：標準 join の左面の公式と joinMap の合成則を使う。
規約：HTT §1.2.8・§1.2.13。使われ方：slice 境界に一致する右単体の面の指定。 -/
lemma cospanJoinRight_face (n : ℕ) (j : Fin (n + 2)) :
    SSet.stdSimplex.δ (j.castAdd 2) ≫ cospanJoinRight.{u} (n + 1) =
      cospanJoinRight n ≫ joinMap (SSet.stdSimplex.δ j) (𝟙 (SSet.horn 2 2 : SSet.{u})) := by
  have h := joinStdSimplexIso_left_face.{u} n j
  have hi : SSet.stdSimplex.δ (j.castAdd 2) ≫ (joinStdSimplexIso (n + 1) 1).inv =
      (joinStdSimplexIso n 1).inv ≫ joinMap (SSet.stdSimplex.δ j) (𝟙 Δ[1]) := by
    apply (cancel_mono (joinStdSimplexIso (n + 1) 1).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h, Iso.inv_hom_id_assoc]
  simp only [cospanJoinRight, ← Category.assoc]
  rw [hi]
  simp only [Category.assoc]
  congr 1
  rw [← joinMap_comp, ← joinMap_comp]
  simp only [Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.DGNerve
