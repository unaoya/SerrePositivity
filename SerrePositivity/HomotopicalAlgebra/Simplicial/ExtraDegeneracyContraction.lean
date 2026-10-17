module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ExtraDegeneracyInterval
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# 追加退化を持つaugmentationはanodyne局所化で可逆となる

## 概要
追加退化を持つaugmentationはanodyne局所化で可逆となる。
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
[棚卸し m0396][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0396
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Extra degeneracies give interval contractions and localized augmentation isomorphisms
-/

@[expose] public section
universe v uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.ExtraDegeneracyContraction
open ExtraDegeneracyInterval
variable {A : SimplicialObject.Augmented (Type v)}
  (ed : SimplicialObject.Augmented.ExtraDegeneracy A)

lemma intervalMap_zero : SSet.ι₀ ≫ intervalMap ed = A.hom ≫ ed.section_ := by
  ext n x
  change A.left.map (SimplexPrefix.cut n.unop (SimplexPrefix.endpoint n.unop 0)).op
      (ed.s n.unop.len x) =
    A.left.map (SimplexCategory.isTerminalZero.from n.unop).op (ed.s' (A.hom.app n x))
  rw [SimplexPrefix.cut_zero_factor]
  simp only [op_comp, A.left.map_comp]
  have hs := types_congr_hom ((extra ed).naturality (SimplexPrefix.zeroVertex n.unop).op) x
  change ed.s 0 (A.left.map (SimplexPrefix.zeroVertex n.unop).op x) =
    A.left.map (SimplexPrefix.functor.map (SimplexPrefix.zeroVertex n.unop)).op
      (ed.s n.unop.len x) at hs
  have he := types_congr_hom ed.s₀_comp_δ₁
    (A.left.map (SimplexPrefix.zeroVertex n.unop).op x)
  change A.left.map (SimplexCategory.δ (1 : Fin 2)).op
      (ed.s 0 (A.left.map (SimplexPrefix.zeroVertex n.unop).op x)) =
    ed.s' (A.hom.app (Opposite.op (SimplexCategory.mk 0))
      (A.left.map (SimplexPrefix.zeroVertex n.unop).op x)) at he
  have ha := types_congr_hom (A.hom.naturality (SimplexPrefix.zeroVertex n.unop).op) x
  change A.hom.app (Opposite.op (SimplexCategory.mk 0))
    (A.left.map (SimplexPrefix.zeroVertex n.unop).op x) = A.hom.app n x at ha
  change A.left.map (SimplexCategory.isTerminalZero.from n.unop).op
      (A.left.map (SimplexCategory.δ (1 : Fin 2)).op
        (A.left.map (SimplexPrefix.functor.map (SimplexPrefix.zeroVertex n.unop)).op
          (ed.s n.unop.len x))) = _
  rw [← hs, he, ha]

lemma intervalMap_one : SSet.ι₁ ≫ intervalMap ed = 𝟙 A.left := by
  ext n x
  change A.left.map (SimplexPrefix.cut n.unop (SimplexPrefix.endpoint n.unop 1)).op
    (ed.s n.unop.len x) = x
  rw [SimplexPrefix.cut_one]
  exact types_congr_hom (ed.s_comp_δ₀ n.unop.len) x

/-- 追加退化から実際の区間ホモトピーによる収縮を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
def contraction : SSet.Homotopy (A.hom ≫ ed.section_) (𝟙 A.left) where
  h := intervalMap ed
  h₀ := intervalMap_zero ed
  h₁ := intervalMap_one ed
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

variable {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
def comparisonIso : L.obj A.left ≅ L.obj ((SimplicialObject.const (Type v)).obj A.right) where
  hom := L.map A.hom
  inv := L.map ed.section_
  hom_inv_id := (L.map_comp _ _).symm.trans
    ((AnodyneHomotopy.map_homotopy_eq L hL (contraction ed)).trans (L.map_id _))
  inv_hom_id := (L.map_comp _ _).symm.trans
    ((congrArg L.map ed.section_comp_hom).trans (L.map_id _))

include ed in
/-- 追加退化を持つaugmentationはanodyne局所化で可逆となる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma localized_augmentation_isIso : IsIso (AnodyneHomotopy.anodyneQ.map A.hom) :=
  (comparisonIso ed AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)).isIso_hom

end SerrePositivity.SimplicialModel.ExtraDegeneracyContraction
