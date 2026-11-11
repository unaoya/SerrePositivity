module

public import SerrePositivity.KST.Spectra.SphereProductDesc

/-!
概要：境界との積からの射は各面との積上で判定できる。
方針：境界の各単体をいずれかの面から持ち上げる。
規約：パラメータに有限性も Kan 性も要求しない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。正方形の四辺の条件の検査。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：境界との積からの二つの射は各面との積上で一致すれば等しい。
方針：境界の面による被覆を単体次数ごとに使う。
規約：正次元の境界と任意のパラメータを扱う。
使われ方：Goerss–Jardine I §7。二つの三角形から貼った写像の境界条件。 -/
theorem boundary_tensor_hom_ext {n : ℕ} {P Y : SSet.{u}}
    {f g : (boundary.{u} (n + 1) : SSet.{u}) ⊗ P ⟶ Y}
    (h : ∀ i : Fin (n + 2), boundary.ι i ▷ P ≫ f = boundary.ι i ▷ P ≫ g) :
    f = g := by
  ext m ⟨⟨x, hx⟩, p⟩
  simp only [boundary_eq_iSup, stdSimplex.face_singleton_compl, Subfunctor.iSup_obj,
    Set.mem_iUnion, Subcomplex.mem_ofSimplex_obj_iff, Opposite.op_unop] at hx
  obtain ⟨i, ⟨y, rfl⟩⟩ := hx
  exact congrArg (fun k : (Δ[n] : SSet.{u}) ⊗ P ⟶ Y => k.app m (⟨y⟩, p)) (h i)

end SerrePositivity.KST.Spectra
