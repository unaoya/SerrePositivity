module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic

/-!
# 同型に沿う部分単体集合と anodyne 性の移送

概要：同型に沿う逆像は元の部分単体集合と同型になり、包含の anodyne 性も保存する。
方針：同型を部分単体集合へ制限して包含の矢印同型を作る。
規約：部分単体集合の逆像を用いる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.12（Tag 00LV） の path 座標への移送。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {X Y : SSet.{u}}

/-- 概要：同型に沿う部分単体集合の逆像は元の部分単体集合と同型である。
方針：同型と逆同型を各次数の部分集合へ制限する。
規約：逆像は順方向の同型に沿う。
使われ方：Kerodon 2.4.5.4（Tag 00LM）・2.4.5.12（Tag 00LV） の path と立方体の比較。 -/
def subcomplexPreimageIso (e : X ≅ Y) (B : Y.Subcomplex) :
    (B.preimage e.hom : SSet) ≅ B where
  hom := {
    app n := ↾fun z ↦ ⟨e.hom.app n z.1, z.2⟩
    naturality := by
      intro n m f
      apply ConcreteCategory.hom_ext
      intro z
      apply Subtype.ext
      exact NatTrans.naturality_apply e.hom f z.1 }
  inv := {
    app n := ↾fun z ↦ ⟨e.inv.app n z.1, by
      change e.hom.app n (e.inv.app n z.1) ∈ B.obj n
      have h := congrArg (fun f ↦ f.app n z.1) e.inv_hom_id
      exact h.symm ▸ z.2⟩
    naturality := by
      intro n m f
      apply ConcreteCategory.hom_ext
      intro z
      apply Subtype.ext
      exact NatTrans.naturality_apply e.inv f z.1 }
  hom_inv_id := by
    apply CategoryTheory.NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact congrArg (fun f ↦ f.app n z.1) e.hom_inv_id
  inv_hom_id := by
    apply CategoryTheory.NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact congrArg (fun f ↦ f.app n z.1) e.inv_hom_id

/-- 概要：同型に沿う逆像の包含は元の包含と矢印同型で結ばれる。
方針：部分単体集合への制限同型と周囲の同型を組み合わせる。
規約：両包含の正方形は厳密に可換である。
使われ方：Kerodon 2.4.5.12（Tag 00LV） の anodyne 性を path へ移す。 -/
def subcomplexPreimageArrowIso (e : X ≅ Y) (B : Y.Subcomplex) :
    Arrow.mk (B.preimage e.hom).ι ≅ Arrow.mk B.ι :=
  Arrow.isoMk (subcomplexPreimageIso e B) e (by rfl)

/-- 概要：anodyne 包含の同型に沿う逆像は anodyne。
方針：包含の矢印同型に沿って性質を移す。
規約：任意の逆像に関する主張ではなく、同型の場合である。
使われ方：HTT 1.1.5.10 の Hom 空間の充填を座標から戻す。 -/
lemma anodyne_subcomplexPreimage (e : X ≅ Y) (B : Y.Subcomplex)
    (hB : SSet.anodyneExtensions B.ι) : SSet.anodyneExtensions (B.preimage e.hom).ι :=
  (SSet.anodyneExtensions.arrow_mk_iso_iff (subcomplexPreimageArrowIso e B)).mpr hB

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
