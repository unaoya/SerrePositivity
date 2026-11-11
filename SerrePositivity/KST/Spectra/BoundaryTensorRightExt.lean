module

public import SerrePositivity.KST.Spectra.BoundaryTensorExt

/-!
概要：第二変数の境界との積からの射を各面で判定する。
方針：境界の面による被覆を各単体次数で使う。
規約：第一変数は任意のパラメータ。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。正方形の横辺の定数性。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：第二変数の境界との積からの射は各面との積で一致すれば等しい。
方針：境界の単体の面への持ち上げを第一変数を固定して使う。
規約：パラメータに Kan 性を要求しない。
使われ方：Goerss–Jardine I §7。正方形の残る二辺の条件。 -/
theorem tensor_boundary_hom_ext {n : ℕ} {P Y : SSet.{u}}
    {f g : P ⊗ (boundary.{u} (n + 1) : SSet.{u}) ⟶ Y}
    (h : ∀ i : Fin (n + 2), P ◁ boundary.ι i ≫ f = P ◁ boundary.ι i ≫ g) :
    f = g := by
  ext m ⟨p, ⟨x, hx⟩⟩
  simp only [boundary_eq_iSup, stdSimplex.face_singleton_compl, Subfunctor.iSup_obj,
    Set.mem_iUnion, Subcomplex.mem_ofSimplex_obj_iff, Opposite.op_unop] at hx
  obtain ⟨i, ⟨y, rfl⟩⟩ := hx
  exact congrArg (fun k : P ⊗ (Δ[n] : SSet.{u}) ⟶ Y => k.app m (p, ⟨y⟩)) (h i)

end SerrePositivity.KST.Spectra
