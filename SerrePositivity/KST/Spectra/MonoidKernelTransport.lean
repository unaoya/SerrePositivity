module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
概要：始域の群同型で前合成した準同型の核を元の核へ移す群同型。
方針：群同型とその逆を部分群に制限し、核の所属条件を合成で計算する。
規約：核の元の値を実際の群同型で写す。
使われ方：Goerss–Jardine VIII §1。通常 Tot と具体的な塔の極限の核の比較。
-/

@[expose] public section
universe u v w
namespace SerrePositivity.KST.Spectra.MonoidKernelTransport

/-- 始域の群同型に沿う核の実際の群同型。 -/
def precomp {G : Type u} {H : Type v} {K : Type w} [Group G] [Group H] [Group K]
    (f : H →* K) (e : G ≃* H) : (f.comp e.toMonoidHom).ker ≃* f.ker where
  toFun x := ⟨e x.val, x.property⟩
  invFun x := ⟨e.symm x.val, by
    change f (e (e.symm x.val)) = 1
    rw [e.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)
  map_mul' x y := Subtype.ext (e.map_mul x.val y.val)

/-- 核の群同型は元の群同型で値を計算する。 -/
@[simp]
lemma precomp_apply_val {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K] (f : H →* K) (e : G ≃* H)
    (x : (f.comp e.toMonoidHom).ker) : (precomp f e x).val = e x.val := rfl

end SerrePositivity.KST.Spectra.MonoidKernelTransport
