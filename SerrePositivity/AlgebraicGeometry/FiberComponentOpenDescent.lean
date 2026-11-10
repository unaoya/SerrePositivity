module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
概要：有限局所自由な標識で選んだファイバー成分の開部分を降下するための補題。
方針：閉写像で一つのファイバーを含む開近傍を基底から取る。
次に二つの引き戻しが等しい開部分を開写像の像として降下する。
規約：閉性と開性は別々の写像に適用できる形にする。
使われ方：Stacks 057I の近傍の縮小と開部分の貼り合わせ。
-/

@[expose] public section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits

universe u

/--
概要：閉写像のあるファイバーを含む開部分に、基底のアフィン近傍の逆像が入る。
方針：開部分の補集合の像を基底から除き、アフィン開基底を使う。
規約：ファイバーは位相空間の点の逆像で表す。
使われ方：標識の二重積の指定ファイバーの近くで、二つの成分の一致を保つ。
-/
theorem exists_affine_open_preimage_le_of_isClosedMap
    {Y S : Scheme.{u}} (g : Y ⟶ S) (hg : IsClosedMap g)
    (s : S) (U : Y.Opens)
    (h : ∀ y : Y, g y = s → y ∈ U) :
    ∃ W : S.Opens, IsAffineOpen W ∧ s ∈ W ∧ g ⁻¹ᵁ W ≤ U := by
  let V : S.Opens := ⟨(g '' (U : Set Y)ᶜ)ᶜ, (hg _ U.2.isClosed_compl).isOpen_compl⟩
  have hs : s ∈ V := by
    rintro ⟨y, hy, hys⟩
    exact hy (h y hys)
  obtain ⟨_, ⟨W, hW, rfl⟩, hsW, hWV⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hs V.2
  refine ⟨W, hW, hsW, fun y hy => ?_⟩
  have hgy : g y ∈ W := hy
  have hyV := hWV hgy
  by_contra hn
  exact hyV ⟨y, hn, rfl⟩

/--
概要：開写像の自己ファイバー積の二つの射で同じ逆像を持つ準コンパクト開は、
基底の準コンパクト開の逆像となる。
方針：開部分の像を取り、自己ファイバー積上の逆像の一致で飽和性を示す。
規約：写像の全射性は仮定しない。
使われ方：標識上で選んだ開部分を元の滑らかな族に降下する。
-/
theorem exists_compact_open_preimage_eq_of_pullback_eq
    {Y X : Scheme.{u}} (f : Y ⟶ X) (hf : IsOpenMap f)
    (U : Y.Opens) (hU : IsCompact (U : Set Y))
    (h : pullback.fst f f ⁻¹ᵁ U = pullback.snd f f ⁻¹ᵁ U) :
    ∃ V : X.Opens, IsCompact (V : Set X) ∧ f ⁻¹ᵁ V = U := by
  let V : X.Opens := ⟨f '' (U : Set Y), hf _ U.2⟩
  refine ⟨V, hU.image f.continuous, ?_⟩
  apply SetLike.ext'
  change f ⁻¹' (f '' (U : Set Y)) = (U : Set Y)
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rw [← Scheme.image_preimage_eq_of_isPullback (IsPullback.of_hasPullback f f)]
  let P : Scheme := pullback f f
  have hset := congrArg (fun W : P.Opens => (W : Set ↥P)) h
  change pullback.fst f f ⁻¹' (U : Set Y) = pullback.snd f f ⁻¹' (U : Set Y) at hset
  rw [hset]
  exact Set.image_preimage_subset _ _

end SerrePositivity.AlgebraicGeometry
