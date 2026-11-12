module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Path
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionFace

/-!
# 閉区間内と周囲の Path Hom の同定

概要：閉区間の任意の二対象の Hom 単体集合は周囲と同型で、単位と合成に整合する。
方針：path の点は端点の間にあることを使い、包含と区間内への引き戻しを互いに逆にする。
規約：有限性、可縮性、充填の仮定は不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の真部分区間からの Hom 回収。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.SimplicialThickening MonoidalCategory

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {J : Type w} [LinearOrder J] {l r : J}
/-- 概要：閉区間内の二対象の間の周囲の path を閉区間内の path として読む。
方針：各点が両端点の間にあることから区間への所属を得る。
規約：任意の線形順序の閉区間を部分型で扱う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の真部分区間上の Hom の回収。 -/
def intervalPathLift {x y : Set.Icc l r} (p : Path x.val y.val) : Path x y where
  I := {z | z.val ∈ p.I}
  left := p.left
  right := p.right
  left_le z hz := p.left_le z.val hz
  le_right z hz := p.le_right z.val hz

/-- 概要：閉区間の path を包含に沿って周囲の path へ送る。
方針：Mathlib の thickening の再添字関手を使う。
規約：任意の線形順序の閉区間を部分型で扱う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の真部分区間上の Hom の回収。 -/
def intervalPathInclusionFunctor (x y : Set.Icc l r) : Path x y ⥤ Path x.val y.val :=
  SimplicialThickening.functorMap ⟨Subtype.val, fun _ _ h ↦ h⟩ (.mk x) (.mk y)
/-- 概要：周囲の path を閉区間内に戻す操作を関手にする。
方針：包含を同じ部分集合へ制限する。
規約：任意の線形順序の閉区間を部分型で扱う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の真部分区間上の Hom の回収。 -/
def intervalPathLiftFunctor (x y : Set.Icc l r) : Path x.val y.val ⥤ Path x y where
  obj := intervalPathLift
  map f := ⟨⟨⟨fun _ hz ↦ f.1.1.1 hz⟩⟩⟩

/-- 概要：閉区間へ戻した path を周囲へ送ると元の path に等しい。
方針：各点が区間に入ることから像の逆向きの所属を構成する。
規約：任意の線形順序の閉区間を部分型で扱う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の真部分区間上の Hom の回収。 -/
lemma intervalPathInclusion_lift (x y : Set.Icc l r) (p : Path x.val y.val) :
    (intervalPathInclusionFunctor x y).obj (intervalPathLift p) = p := by
  apply Path.ext
  ext z
  change (∃ t : Set.Icc l r, t.val ∈ p.I ∧ t.val = z) ↔ z ∈ p.I
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hz
    exact ⟨⟨z, ⟨x.property.1.trans (p.left_le z hz),
      (p.le_right z hz).trans y.property.2⟩⟩, hz, rfl⟩
/-- 概要：閉区間の path を周囲へ送り戻すと元の path に等しい。
方針：部分型の値の単射性で像の所属を比較する。
規約：任意の線形順序の閉区間を部分型で扱う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の真部分区間上の Hom の回収。 -/
lemma intervalPathLift_inclusion (x y : Set.Icc l r) (p : Path x y) :
    intervalPathLift ((intervalPathInclusionFunctor x y).obj p) = p := by
  apply Path.ext
  ext z
  change (∃ t : Set.Icc l r, t ∈ p.I ∧ t.val = z.val) ↔ z ∈ p.I
  constructor
  · rintro ⟨t, ht, he⟩
    exact Subtype.ext he ▸ ht
  · intro hz
    exact ⟨z, hz, rfl⟩
/-- 概要：閉区間の包含と引き戻しの関手の合成は恒等関手である。
方針：対象上の逆写像性と射の薄さを使う。
規約：任意の線形順序の閉区間を部分型で扱う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の真部分区間上の Hom の回収。 -/
lemma intervalPathInclusion_comp_lift (x y : Set.Icc l r) :
    intervalPathInclusionFunctor x y ⋙ intervalPathLiftFunctor x y = 𝟭 (Path x y) :=
  CategoryTheory.Functor.ext (fun p ↦ intervalPathLift_inclusion x y p)
/-- 概要：周囲からの引き戻しと包含の関手の合成は恒等関手である。
方針：対象上の逆写像性と射の薄さを使う。
規約：任意の線形順序の閉区間を部分型で扱う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の真部分区間上の Hom の回収。 -/
lemma intervalPathLift_comp_inclusion (x y : Set.Icc l r) :
    intervalPathLiftFunctor x y ⋙ intervalPathInclusionFunctor x y = 𝟭 (Path x.val y.val) :=
  CategoryTheory.Functor.ext (fun p ↦ intervalPathInclusion_lift x y p)
/-- 概要：閉区間の任意の二対象の Hom 単体集合は周囲の Hom 単体集合と同型である。
方針：互いに逆の関手の nerve を取る。
規約：任意の線形順序の閉区間を部分型で扱う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の真部分区間上の Hom の回収。 -/
def intervalPathHomIso (x y : Set.Icc l r) : nerve (Path x y) ≅ nerve (Path x.val y.val) where
  hom := nerveMap (intervalPathInclusionFunctor x y)
  inv := nerveMap (intervalPathLiftFunctor x y)
  hom_inv_id := by
    change nerveMap (intervalPathInclusionFunctor x y ⋙ intervalPathLiftFunctor x y) =
      nerveMap (𝟭 _)
    rw [intervalPathInclusion_comp_lift]
  inv_hom_id := by
    change nerveMap (intervalPathLiftFunctor x y ⋙ intervalPathInclusionFunctor x y) =
      nerveMap (𝟭 _)
    rw [intervalPathLift_comp_inclusion]
/-- 概要：閉区間の Hom 同型の順写像は native な包含の Hom 写像である。
方針：thickening と nerveMap の定義を使う。
規約：任意の線形順序の閉区間を部分型で扱う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の真部分区間上の Hom の回収。 -/
lemma intervalPathHomIso_hom (x y : Set.Icc l r) :
    (intervalPathHomIso x y).hom =
      (SimplicialThickening.functor (⟨Subtype.val, fun _ _ h ↦ h⟩ : Set.Icc l r →o J)).map
        (.mk x) (.mk y) := rfl
/-- 概要：閉区間の Hom 同型は native な合成に整合する。
方針：区間の包含の豊穣関手の合成の法則を使う。
規約：任意の線形順序の閉区間を部分型で扱う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の真部分区間上の Hom の回収。 -/
lemma intervalPathHomIso_comp (x y z : Set.Icc l r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap x y z ≫ (intervalPathHomIso x z).hom =
      ((intervalPathHomIso x y).hom ⊗ₘ (intervalPathHomIso y z).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap x.val y.val z.val :=
  (SimplicialThickening.functor
    (⟨Subtype.val, fun _ _ h ↦ h⟩ : Set.Icc l r →o J)).map_comp (.mk x) (.mk y) (.mk z)
/-- 概要：閉区間の Hom 同型は native な単位に整合する。
方針：区間の包含の豊穣関手の単位の法則を使う。
規約：任意の線形順序の閉区間を部分型で扱う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の真部分区間上の Hom の回収。 -/
lemma intervalPathHomIso_id (x : Set.Icc l r) :
    eId SSet (SimplicialThickening.mk x) ≫ (intervalPathHomIso x x).hom =
      eId SSet (SimplicialThickening.mk x.val) :=
  (SimplicialThickening.functor
    (⟨Subtype.val, fun _ _ h ↦ h⟩ : Set.Icc l r →o J)).map_id (.mk x)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
