module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.Connected.Basic

/-!
概要：スキーム射の切断を通るファイバー成分の集合を定める。
方針：位相ファイバーの連結成分を取り、埋め込みによる底変換と比較する。
規約：埋め込みの場合の比較は、引き戻しの点の像とファイバーの同一視に従う。
使われ方：基底の既約閉部分と主開への制限で構成可能性を判定する。
-/

@[expose] public section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits Set Topology

/--
概要：位相的埋め込みは、部分集合内の連結成分を像の中の連結成分に移す。
方針：連結成分の逆像が前連結であることを、誘導位相で確かめる。
規約：指定点は部分集合に属するとする。
使われ方：主開と閉部分への制限でファイバー成分を比較する。
-/
theorem image_connectedComponentIn_of_embedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {i : X → Y}
    (hi : IsEmbedding i) {F : Set X} {x : X} (hx : x ∈ F) :
    i '' connectedComponentIn F x = connectedComponentIn (i '' F) (i x) := by
  let W := connectedComponentIn (i '' F) (i x)
  have hWF : W ⊆ i '' F := connectedComponentIn_subset _ _
  have hRange : W ⊆ range i := hWF.trans (image_subset_range _ _)
  have hImage : i '' (i ⁻¹' W) = W := by
    rw [image_preimage_eq_inter_range, inter_eq_left.mpr hRange]
  have hConnected : IsPreconnected (i ⁻¹' W) := by
    apply hi.isInducing.isPreconnected_image.mp
    rw [hImage]
    exact isPreconnected_connectedComponentIn
  have hx' : x ∈ i ⁻¹' W := mem_connectedComponentIn (mem_image_of_mem _ hx)
  have hSub : i ⁻¹' W ⊆ F := fun _ hy => hi.injective.mem_set_image.mp (hWF hy)
  have hIncl := hConnected.subset_connectedComponentIn hx' hSub
  apply (hi.continuous.continuousOn.image_connectedComponentIn_subset hx).antisymm
  change W ⊆ i '' connectedComponentIn F x
  rw [← hImage]
  exact image_mono hIncl

/--
概要：射の切断を通るファイバー成分に属する点の集合。
方針：各点の像を通るファイバーの中で切断の像との連結性を取る。
規約：ファイバーは台の一点の逆像として表す。
使われ方：滑らかな族の成分の開性と降下。
-/
def sectionComponentLocus {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X) : Set X :=
  {x | x ∈ connectedComponentIn (f ⁻¹' {f x}) (s (f x))}

/--
概要：埋め込みに沿うスキームの引き戻しでは、切断を通るファイバー成分の集合は逆像に一致する。
方針：引き戻しの点の像を使って位相ファイバーを同定し、埋め込みで成分を比較する。
規約：二つの切断が引き戻しの四角形と両立するとする。
使われ方：構成可能性を基底の既約閉部分上で判定する。
-/
theorem preimage_sectionComponentLocus_of_isPullback_of_isEmbedding
    {P X Y S : Scheme.{u}} {i : P ⟶ X} {f' : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback i f' f g) (hi : IsEmbedding i)
    (s : S ⟶ X) (s' : Y ⟶ P) (hs' : s' ≫ f' = 𝟙 Y) (hs : s' ≫ i = g ≫ s) :
    i ⁻¹' sectionComponentLocus f s = sectionComponentLocus f' s' := by
  ext x
  have hx := congrArg (fun j : P ⟶ S => j x) h.w
  simp only [Scheme.Hom.comp_apply] at hx
  have hx' : s' (f' x) ∈ f' ⁻¹' {f' x} := by
    change f' (s' (f' x)) = f' x
    have e := congrArg (fun j : Y ⟶ Y => j (f' x)) hs'
    simpa [Scheme.Hom.comp_apply] using e
  have hImage : i '' (f' ⁻¹' {f' x}) = f ⁻¹' {f (i x)} := by
    rw [Scheme.image_preimage_eq_of_isPullback h.flip, image_singleton, ← hx]
  have hPoint : i (s' (f' x)) = s (f (i x)) := by
    have e := congrArg (fun j : Y ⟶ X => j (f' x)) hs
    simpa only [Scheme.Hom.comp_apply, hx] using e
  have hComp := image_connectedComponentIn_of_embedding hi hx'
  rw [hImage, hPoint] at hComp
  change i x ∈ connectedComponentIn (f ⁻¹' {f (i x)}) (s (f (i x))) ↔
    x ∈ connectedComponentIn (f' ⁻¹' {f' x}) (s' (f' x))
  rw [← hComp]
  exact hi.injective.mem_set_image

end SerrePositivity.AlgebraicGeometry
