module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionFace
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathFaces

/-!
# Path の零座標面と合成面の交わり

概要：面内 Hom の直積は零座標面と合成面の交わりと同型になる。
方針：面写像と合成写像の像、逆像、単射性を計算して像との同型を取る。
規約：追加の充填や順序の仮定を導入しない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の混合した重なりの整合性。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v

open CategoryTheory MonoidalCategory CategoryTheory.SimplicialThickening

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {n : ℕ}
/-- 概要：面内の二つの Hom の合成を周囲の Hom へ送る写像を定義する。
方針：両 Hom に面写像を適用し、native な合成を取る。
規約：Mathlib の native な Path Hom と包含を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面と合成面の混合した重なり。 -/
def pathFaceCompositionMap (j : Fin (n + 2)) (a b c : Fin (n + 1)) :
    nerve (Path (ULift.up.{v} a) (ULift.up.{v} b)) ⊗
      nerve (Path (ULift.up.{v} b) (ULift.up.{v} c)) ⟶
        nerve (Path (ULift.up.{v} (j.succAbove a)) (ULift.up.{v} (j.succAbove c))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap j a b ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap j b c) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (j.succAbove a)) (ULift.up (j.succAbove b))
      (ULift.up (j.succAbove c))
/-- 概要：面内で合成してから面へ送る操作は周囲での合成に等しい。
方針：thickening の面の豊穣関手の合成則を使う。
規約：Mathlib の native な Path Hom と包含を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面と合成面の混合した重なり。 -/
lemma pathFaceCompositionMap_eq_native (j : Fin (n + 2)) (a b c : Fin (n + 1)) :
    pathFaceCompositionMap.{v} j a b c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up.{v} a) (ULift.up.{v} b) (ULift.up.{v} c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap j a c :=
  ((SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map_comp
    ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ⟨⟨c⟩⟩).symm
/-- 概要：切断点を通る合成面を面写像で引き戻すと対応する合成面になる。
方針：succAbove による像の所属と単射性を使う。
規約：Mathlib の native な Path Hom と包含を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面と合成面の混合した重なり。 -/
lemma pathThrough_preimage_pathFaceMap (j : Fin (n + 2)) (a b c : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up.{v} (j.succAbove a))
      (c := ULift.up (j.succAbove c)) (ULift.up (j.succAbove b))).preimage
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap j a c) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up a) (c := ULift.up c) (ULift.up b) := by
  ext m F
  change (∀ t, ULift.up (j.succAbove b) ∈
    (SimplexCategory.δ j).toOrderHom.uliftMap '' (F.obj t).I) ↔
      ∀ t, ULift.up b ∈ (F.obj t).I
  constructor
  · intro h t
    obtain ⟨x, hx, he⟩ := h t
    have he' : x = ULift.up b := by
      apply ULift.ext
      exact (Fin.strictMono_succAbove j).injective (congrArg ULift.down he)
    exact he' ▸ hx
  · intro h t
    exact ⟨ULift.up b, h t, rfl⟩
/-- 概要：面内 Hom の合成の像は零座標面と合成面の交わりである。
方針：合成面の逆像、像と逆像の一般計算、面写像の像の等式を使う。
規約：Mathlib の native な Path Hom と包含を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面と合成面の混合した重なり。 -/
lemma range_pathFaceCompositionMap (j : Fin (n + 2)) (a b c : Fin (n + 1)) :
    SSet.Subcomplex.range (pathFaceCompositionMap.{v} j a b c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (j.succAbove b)) := by
  rw [pathFaceCompositionMap_eq_native, SSet.Subcomplex.range_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.range_pathCompMap,
    ← pathThrough_preimage_pathFaceMap j a b c]
  have hgen {X Y : SSet.{v}} (f : X ⟶ Y) (B : Y.Subcomplex) :
      (B.preimage f).image f = SSet.Subcomplex.range f ⊓ B := by
    ext m y
    change (∃ x, f.app m x ∈ B.obj m ∧ f.app m x = y) ↔
      ((∃ x, f.app m x = y) ∧ y ∈ B.obj m)
    aesop
  rw [hgen, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.range_pathFaceMap]
/-- 概要：面内 Hom の合成を周囲へ送る写像は単射である。
方針：native な合成と面写像の単射性を合成する。
規約：Mathlib の native な Path Hom と包含を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面と合成面の混合した重なり。 -/
lemma pathFaceCompositionMap_mono (j : Fin (n + 2)) (a b c : Fin (n + 1)) :
    Mono (pathFaceCompositionMap.{v} j a b c) := by
  rw [pathFaceCompositionMap_eq_native]
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap_mono (ULift.up.{v} a) (ULift.up.{v} b) (ULift.up.{v} c)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap_mono.{v} j a c
  infer_instance
/-- 概要：面内 Hom の直積を零座標面と合成面の交わりと同型にする。
方針：単射をその像へ移し、像の等式を適用する。
規約：Mathlib の native な Path Hom と包含を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面と合成面の混合した重なり。 -/
noncomputable def pathMixedFaceIso (j : Fin (n + 2)) (a b c : Fin (n + 1)) :
    nerve (Path (ULift.up.{v} a) (ULift.up.{v} b)) ⊗
      nerve (Path (ULift.up.{v} b) (ULift.up.{v} c)) ≅
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up (j.succAbove a)) (b := ULift.up (j.succAbove c))
          (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (j.succAbove b)) :
            (nerve (Path (ULift.up (j.succAbove a)) (ULift.up (j.succAbove c)))).Subcomplex) := by
  letI := pathFaceCompositionMap_mono.{v} j a b c
  exact asIso (SSet.Subcomplex.toRange (pathFaceCompositionMap j a b c)) ≪≫
    SSet.Subcomplex.eqToIso (range_pathFaceCompositionMap j a b c)
/-- 概要：混合した交わりとの同型と包含の合成は native な面内 Hom の合成である。
方針：像への因子分解の定義を使う。
規約：Mathlib の native な Path Hom と包含を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面と合成面の混合した重なり。 -/
lemma pathMixedFaceIso_hom_ι (j : Fin (n + 2)) (a b c : Fin (n + 1)) :
    (pathMixedFaceIso.{v} j a b c).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up (j.succAbove a)) (b := ULift.up (j.succAbove c))
        (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (j.succAbove b))).ι =
          pathFaceCompositionMap j a b c := rfl
/-- 概要：混合した交わりから合成面への写像は両 Hom の面写像と合成面の同型で表せる。
方針：部分単体集合の包含と像への因子分解の定義を比較する。
規約：Mathlib の native な Path Hom と包含を使う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面と合成面の混合した重なり。 -/
lemma pathMixedFaceIso_hom_toThrough (j : Fin (n + 2)) (a b c : Fin (n + 1)) :
    (pathMixedFaceIso.{v} j a b c).hom ≫ SSet.Subcomplex.homOfLE
      (show (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up (j.succAbove a)) (b := ULift.up (j.succAbove c))
        (ULift.up j) ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (j.succAbove b))) ≤
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (j.succAbove b)) from inf_le_right) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap j a b ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap j b c) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso (ULift.up (j.succAbove a)) (ULift.up (j.succAbove b))
          (ULift.up (j.succAbove c))).hom := rfl

/-- 概要：同じ点を避ける零座標面とその点を通る合成面の交わりは空である。
方針：任意の単体の最初の頂点で所属と非所属が矛盾する。
規約：任意の線形順序の端点と切断点に対して扱う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の同じ座標の混合した重なり。 -/
lemma pathMixed_self_eq_bot {J : Type v} [LinearOrder J] (a b c : J) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := a) (b := c) b ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := a) (c := c) b) = ⊥ := by
  ext m F
  change ((∀ t, b ∉ (F.obj t).I) ∧ ∀ t, b ∈ (F.obj t).I) ↔ False
  exact ⟨fun h ↦ h.1 0 (h.2 0), False.elim⟩

/-- 概要：同じ点に関する空の混合した交わりからの写像は一意である。
方針：各次数の単体は所属と非所属の矛盾を持つ。
規約：行き先は任意の単体集合でよい。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の貼合せで空の交わりの整合性を消去する。 -/
lemma pathMixed_self_hom_ext {J : Type v} [LinearOrder J] (a b c : J) {X : SSet.{v}}
    (f g : ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := a) (b := c) b ⊓ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := a) (c := c) b :
      (nerve (Path a c)).Subcomplex) : SSet) ⟶ X) :
    f = g := by
  apply CategoryTheory.NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro z
  have hz : (∀ t, b ∉ (z.1.obj t).I) ∧ ∀ t, b ∈ (z.1.obj t).I := z.2
  exact (hz.1 0 (hz.2 0)).elim

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
