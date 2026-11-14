module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Comparison.GroupCompletion
public import Mathlib.Data.Quot

/-!
# 単体的モノイドの連結成分と群状性

概要：一般の単体的モノイドの π₀ の演算と群状性の条件を与える。
方針：辺の積を用いて商へ乗法を降ろし、全成分の可逆性を述べる。
規約：群状性は各次数の群構造を意味しない。Segal 1974 Proposition 1.5。
使われ方：bar 分類空間による群完備化の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.Comparison

open CategoryTheory Opposite SSet
open scoped Simplicial

/--
概要：単体的モノイドの台単体集合。
方針：モノイドから型への忘却関手を合成する。
規約：KST Lemma 2.13、Segal 1974 Proposition 1.5 の乗法空間。
使われ方：π₀ のモノイドと群状性。
-/
abbrev monoidSpace (M : SimplicialObject MonCat.{u}) : SSet.{u} := M ⋙ forget MonCat

namespace SimplicialMonoid

variable (M : SimplicialObject MonCat.{u})

local instance (n : SimplexCategoryᵒᵖ) : Monoid ((monoidSpace M).obj n) :=
  inferInstanceAs (Monoid (M.obj n))

/--
概要：単体的モノイドの二本の辺を掛ける。
方針：一次単体の積を取り、両面でモノイド準同型性を使う。
規約：非可換の順序を保つ。Segal 1974 Proposition 1.5 の入力。
使われ方：π₀ の乗法の代表独立性。
-/
def edgeMul {a b c d : M.obj (op ⦋0⦌)} (e : (monoidSpace M).Edge a b)
    (f : (monoidSpace M).Edge c d) : (monoidSpace M).Edge (a * c) (b * d) :=
  .mk (e.edge * f.edge)
    (by change (M.map (SimplexCategory.δ 1).op).hom (e.edge * f.edge) = _
        rw [map_mul]; exact congrArg₂ (· * ·) e.src_eq f.src_eq)
    (by change (M.map (SimplexCategory.δ 0).op).hom (e.edge * f.edge) = _
        rw [map_mul]; exact congrArg₂ (· * ·) e.tgt_eq f.tgt_eq)

unseal SSet.π₀ in
/--
概要：π₀ の積を零次単体の積で定める。
方針：辺の積から二重商への写像を定義する。
規約：Segal 1974 Proposition 1.5 の群状性で使う積。
使われ方：π₀ のモノイド構造。
-/
def componentsMul : π₀ (monoidSpace M) → π₀ (monoidSpace M) → π₀ (monoidSpace M) :=
  Quot.lift₂ (fun a b => π₀.mk (a * b))
    (by rintro a b c ⟨e⟩; exact π₀.sound (edgeMul M (.id a) e))
    (by rintro a b c ⟨e⟩; exact π₀.sound (edgeMul M e (.id c)))

/--
概要：単体的モノイドの連結成分のモノイド。
方針：商の積と単位を定義し、各法則を零次の代表で検証する。
規約：型クラスの重複を避けるため明示的な構造として渡す。KST Lemma 2.13。
使われ方：一般の群状性の定義。
-/
@[instance_reducible] def componentsMonoid : Monoid (π₀ (monoidSpace M)) where
  mul := componentsMul M
  one := π₀.mk (1 : M.obj (op ⦋0⦌))
  mul_assoc a b c := by
    induction a using π₀.rec with | mk a => ?_
    induction b using π₀.rec with | mk b => ?_
    induction c using π₀.rec with | mk c => exact congrArg π₀.mk (mul_assoc a b c)
  one_mul a := by
    induction a using π₀.rec with | mk a => exact congrArg π₀.mk (one_mul a)
  mul_one a := by
    induction a using π₀.rec with | mk a => exact congrArg π₀.mk (mul_one a)

/--
概要：群状性は π₀ の全ての成分が乗法で可逆であること。
方針：実際の零次単体の積から誘導したモノイドの単元性で述べる。
規約：各単体次数の逆元は要求しない。Segal 1974 Proposition 1.5。
使われ方：ĜL の分類空間による delooping。
-/
def IsGrouplike : Prop :=
  letI := componentsMonoid M
  ∀ a : π₀ (monoidSpace M), IsUnit a

/--
概要：群状単体的モノイドの π₀ に誘導乗法を保つ群構造を付ける。
方針：各成分の単元性から逆元を選ぶ。
規約：乗法と単位は `componentsMonoid` のまま保持する。KST Lemma 2.13。
使われ方：分類空間の π₁ の群としての比較。
-/
@[instance_reducible] noncomputable def componentsGroup (h : IsGrouplike M) :
    Group (π₀ (monoidSpace M)) := by
  letI := componentsMonoid M
  exact
    { componentsMonoid M with
      inv := fun a => ((h a).unit⁻¹ : (π₀ (monoidSpace M))ˣ)
      inv_mul_cancel := fun a => by
        change ((h a).unit⁻¹ : (π₀ (monoidSpace M))ˣ).val * a = 1
        rw [← (h a).unit_spec]
        exact Units.inv_mul (h a).unit }

end SimplicialMonoid

end SerrePositivity.KST.Comparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "5.2.6.4" (partial := component) "仮定：厳密単体的モノイド M の π₀ の全成分が単元（Lean が強い：厳密模型と π₀ による条件を指定）。結論：π₀ に誘導乗法を保つ群構造が付き、各頂点の左平行移動は anodyne 局所化で可逆となる（原典の π₀ の群性と左平行移動の同値という部分に一致）。全 E₁ 空間の shear 判定の両方向と右側は含まれない。"] _root_.SerrePositivity.KST.Comparison.SimplicialMonoid.componentsGroup
