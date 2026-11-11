module

public import SerrePositivity.AlgebraicGeometry.SectionComponentLocus
public import SerrePositivity.AlgebraicGeometry.FiberComponentOpenDescent

/-!
概要：閉写像のファイバー上で同じ成分を選ぶ二つの切断は、基底を縮めると同じ成分を選ぶ。
方針：片方の切断による他方の成分の逆像を取り、その中に指定ファイバーの近傍を取る。
規約：成分の開性は仮定として与える。
使われ方：有限局所自由な標識の自己ファイバー積で成分の逆像を比較する。
-/

@[expose] public section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory

/--
概要：閉写像の指定ファイバーで二つの切断が同じ成分を選ぶなら、
基底を指定点のアフィン開近傍に縮めても両者の成分が一致する。
方針：一方の切断が他方の成分に入る開部分を、閉写像を使って基底から取る。
規約：切断を通る成分は位相ファイバー内の連結成分とする。
使われ方：Stacks 057I の有限局所自由な標識からの開部分の降下。
-/
theorem exists_affine_open_sectionComponentLoci_agree_of_isClosedMap
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (s t : Y ⟶ X) (q : Y ⟶ S)
    (hs : s ≫ f = 𝟙 Y) (hq : IsClosedMap q)
    (ht : IsOpen (sectionComponentLocus f t)) (a : S)
    (h : ∀ y : Y, q y = a → s y ∈ sectionComponentLocus f t) :
    ∃ U : S.Opens, IsAffineOpen U ∧ a ∈ U ∧
      sectionComponentLocus f s ∩ (f ≫ q) ⁻¹' (U : Set S) =
        sectionComponentLocus f t ∩ (f ≫ q) ⁻¹' (U : Set S) := by
  let W : Y.Opens := ⟨s ⁻¹' sectionComponentLocus f t, ht.preimage s.continuous⟩
  obtain ⟨U, hU, ha, hUW⟩ := exists_affine_open_preimage_le_of_isClosedMap q hq a W h
  refine ⟨U, hU, ha, ?_⟩
  ext x
  change (x ∈ sectionComponentLocus f s ∧ q (f x) ∈ U) ↔
    (x ∈ sectionComponentLocus f t ∧ q (f x) ∈ U)
  refine and_congr_left_iff.mpr fun hx => ?_
  have hfx : f (s (f x)) = f x := by
    have e := congrArg (fun k : Y ⟶ Y => k (f x)) hs
    simpa [Scheme.Hom.comp_apply] using e
  have hm : s (f x) ∈ sectionComponentLocus f t := hUW hx
  change s (f x) ∈ connectedComponentIn (f ⁻¹' {f (s (f x))}) (t (f (s (f x)))) at hm
  rw [hfx] at hm
  change x ∈ connectedComponentIn (f ⁻¹' {f x}) (s (f x)) ↔
    x ∈ connectedComponentIn (f ⁻¹' {f x}) (t (f x))
  rw [connectedComponentIn_eq hm]

end SerrePositivity.AlgebraicGeometry
