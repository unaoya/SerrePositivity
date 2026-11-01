module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneIntervalEndpoints
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# anodyne射を反転する関手は単体的にホモトピックな二射を同じ射へ送る

## 概要
anodyne射を反転する関手は単体的にホモトピックな二射を同じ射へ送る。
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
[棚卸し m0340][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0340
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Full simplicial homotopies are inverted by anodyne-inverting functors

Only the canonical interval and ordinary categorical inverses are used.
No full simplicial model structure is needed in the source universe.
-/

@[expose] public section
universe v vH uH
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.AnodyneHomotopy
variable {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

lemma endpoint_projection_zero (X : SSet.{v}) :
    SSet.ι₀ ≫ fst X (SSet.stdSimplex.obj (SimplexCategory.mk 1)) = 𝟙 X := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

lemma endpoint_projection_one (X : SSet.{v}) :
    SSet.ι₁ ≫ fst X (SSet.stdSimplex.obj (SimplexCategory.mk 1)) = 𝟙 X := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

include hL in
lemma endpoint_images_eq (X : SSet.{v}) :
    L.map (SSet.ι₀ (X := X)) = L.map (SSet.ι₁ (X := X)) := by
  let p := fst X (SSet.stdSimplex.obj (SimplexCategory.mk 1))
  have : IsIso (L.map (SSet.ι₀ (X := X))) := hL _ (endpoint_zero_anodyne X)
  have hp₀ : L.map (SSet.ι₀ (X := X)) ≫ L.map p = 𝟙 _ := by
    rw [← L.map_comp, endpoint_projection_zero, L.map_id]
  have : IsIso (L.map p) := (isIso_comp_left_iff (L.map (SSet.ι₀ (X := X))) _).mp
    (hp₀.symm ▸ inferInstanceAs (IsIso (𝟙 (L.obj X))))
  apply (cancel_mono (L.map p)).mp
  rw [← L.map_comp, ← L.map_comp, endpoint_projection_zero, endpoint_projection_one]

include hL in
/-- anodyne射を反転する関手は単体的にホモトピックな二射を同じ射へ送る。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma map_homotopy_eq {X Y : SSet.{v}} {f g : X ⟶ Y} (h : SSet.Homotopy f g) :
    L.map f = L.map g := by
  calc
    L.map f = L.map SSet.ι₀ ≫ L.map h.h :=
      (congrArg L.map h.h₀).symm.trans (L.map_comp _ _)
    _ = L.map SSet.ι₁ ≫ L.map h.h :=
      congrArg (fun k => k ≫ L.map h.h) (endpoint_images_eq L hL X)
    _ = L.map g := (L.map_comp _ _).symm.trans (congrArg L.map h.h₁)

/-- The actual section and the same all-degree homotopy give an ordinary inverse. -/
def mapRetractionIso {X Y : SSet.{v}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) (h : SSet.Homotopy (𝟙 X) (f ≫ s)) : L.obj X ≅ L.obj Y where
  hom := L.map f
  inv := L.map s
  hom_inv_id := (L.map_comp _ _).symm.trans
    ((map_homotopy_eq L hL h).symm.trans (L.map_id _))
  inv_hom_id := (L.map_comp _ _).symm.trans ((congrArg L.map hs).trans (L.map_id _))

/-- Ordinary localization of the canonical anodyne class, in any value universe. -/
abbrev anodyneQ := SSet.anodyneExtensions.{v}.Q

include hL in
lemma map_isIso_of_anodyneQ_isIso {X Y : SSet.{v}} (f : X ⟶ Y)
    (hf : IsIso (anodyneQ.map f)) : IsIso (L.map f) := by
  let G := Localization.lift L hL anodyneQ
  let e : anodyneQ ⋙ G ≅ L := Localization.fac L hL anodyneQ
  have : IsIso (G.map (anodyneQ.map f)) := inferInstance
  let ea : Arrow.mk (G.map (anodyneQ.map f)) ≅ Arrow.mk (L.map f) :=
    Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm
  exact ((MorphismProperty.isomorphisms H).arrow_mk_iso_iff ea).mp inferInstance

end SerrePositivity.SimplicialModel.AnodyneHomotopy
