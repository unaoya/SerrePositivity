module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNaturalMatching

/-!
# 各成分のすべての単射に対する右持ち上げ性から相対matching射の右持ち上げ性を導く

## 概要
各成分のすべての単射に対する右持ち上げ性から相対matching射の右持ち上げ性を導く。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0561][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0561
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Matching lifting from objectwise right lifting against all monomorphisms

This argument uses finite matching calculations, with no model structure
in the value universe. It applies to large auxiliary parameter spaces.
-/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.SimplexMonomorphismLifting
variable (X : SSet.{w}) (A B : X.Elementsᵒᵖ ⥤ SSet.{v}) (p : A ⟶ B)
  (hA : ∀ {a b : X.Elementsᵒᵖ} (f : a ⟶ b),
    (elementsDirect (direct := simplexInverse.op) X).op f → IsIso (A.map f))
  (hB : ∀ {a b : X.Elementsᵒᵖ} (f : a ⟶ b),
    (elementsDirect (direct := simplexInverse.op) X).op f → IsIso (B.map f))
  (hp : ∀ s, (MorphismProperty.monomorphisms SSet.{v}).rlp (p.app s))

include hA hB hp in
/-- 各成分のすべての単射に対する右持ち上げ性から相対matching射の右持ち上げ性を導く。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma relativeMatching_rightLifting (s : X.Elementsᵒᵖ) :
    (MorphismProperty.monomorphisms SSet.{v}).rlp
      (relativeMatchingMap (SimplexIndexFinite.reedy X) s p) := by
  classical
  by_cases h : Nonempty (SimplexMatchingTerminal.Index X s)
  · have : Nonempty (SimplexMatchingTerminal.Index X s) := h
    have : IsIso ((matchingComparison (SimplexIndexFinite.reedy X) s).app A) :=
      SimplexMatchingTerminal.matchingComparison_isIso X s A hA
    have : IsIso ((matchingComparison (SimplexIndexFinite.reedy X) s).app B) :=
      SimplexMatchingTerminal.matchingComparison_isIso X s B hB
    have hi : Arrow.mk (relativeMatchingMap (SimplexIndexFinite.reedy X) s p) ≅
        Arrow.mk ((matchingComparison (SimplexIndexFinite.reedy X) s).app A) :=
      Arrow.isoMk (Iso.refl _)
        (asIso (pullback.snd ((matchingComparison (SimplexIndexFinite.reedy X) s).app B)
          ((matchingEvaluation (SimplexIndexFinite.reedy X) s).map p))) (by
            change (𝟙 _) ≫ _ = pullback.lift _ _ _ ≫ pullback.snd _ _
            rw [Category.id_comp, pullback.lift_snd]
            rfl)
    apply (((MorphismProperty.monomorphisms SSet.{v}).rlp).arrow_iso_iff hi).mpr
    change (MorphismProperty.monomorphisms SSet.{v}).rlp
      ((matchingComparison (SimplexIndexFinite.reedy X) s).app A)
    exact (MorphismProperty.monomorphisms SSet.{v}).rlp_of_isIso _
  · have : IsEmpty (SimplexMatchingTerminal.Index X s) := not_nonempty_iff.mp h
    have : IsIso ((matchingEvaluation (SimplexIndexFinite.reedy X) s).map p) :=
      isIso_of_isTerminal (SimplexInverseMatching.emptyMatchingTerminal X s A)
        (SimplexInverseMatching.emptyMatchingTerminal X s B) _
    have hi : Arrow.mk (relativeMatchingMap (SimplexIndexFinite.reedy X) s p) ≅
        Arrow.mk (p.app s) := Arrow.isoMk (Iso.refl _)
          (asIso (pullback.fst ((matchingComparison (SimplexIndexFinite.reedy X) s).app B)
            ((matchingEvaluation (SimplexIndexFinite.reedy X) s).map p))) (by
              change (𝟙 _) ≫ _ = pullback.lift _ _ _ ≫ pullback.fst _ _
              rw [Category.id_comp, pullback.lift_fst]
              rfl)
    apply (((MorphismProperty.monomorphisms SSet.{v}).rlp).arrow_iso_iff hi).mpr
    change (MorphismProperty.monomorphisms SSet.{v}).rlp (p.app s)
    exact hp s

include hA hB hp in
lemma reedyRight : Reedy.reedyRight (SimplexIndexFinite.reedy X)
    ((MorphismProperty.monomorphisms SSet.{v}).rlp) p :=
  fun s => relativeMatching_rightLifting X A B p hA hB hp s

end SerrePositivity.SimplicialModel.SimplexMonomorphismLifting
