module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.Pi.Basic

/-!
概要：群の関数群の加法的表示と加法的係数の関数群の比較。
方針：各座標で Additive のタグを付け外しする。
規約：添字集合は任意。群の可換性を要求しない。
使われ方：Goerss–Jardine VIII §2。乗法的 π_* の cochain と線形な加法的 cochain の橋渡し。
-/

@[expose] public section

universe u

namespace SerrePositivity.KST.Spectra

/-- 概要：関数群の加法的表示は加法的な係数を持つ関数群と同型。
方針：タグの付け外しを座標ごとに行う。
規約：元の群は非可換でもよい。
使われ方：Goerss–Jardine VIII §2。π_* の関数群を加法的 cochain に直す。 -/
def additiveFunctionEquiv (S M : Type u) [Group M] : Additive (S → M) ≃+ (S → Additive M) where
  toFun x s := Additive.ofMul (x.toMul s)
  invFun y := Additive.ofMul (fun s ↦ (y s).toMul)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end SerrePositivity.KST.Spectra
