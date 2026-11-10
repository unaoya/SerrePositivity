module

public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.PowerTorsion
public import SerrePositivity.HomologicalAlgebra.TorSequentialColimits
import SerrePositivity.HomologicalAlgebra.TorSymmetry
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Module.LocalizedModule.Away

/-!
# 完全平坦性と主局所化による Tor の消滅

## 概要
a 完全平坦な加群と、a 正則かつ a を逆にすると平坦な加群との高次 Tor は零。

## 方針
局所化への単射の余核を、a の冪ごとの零化部分加群の有向和として扱う。
高次 Tor は各段で零となり、局所化と余核の短完全列から元の加群へ戻る。

## 規約
環の Noether 性を仮定しない。

## 使われ方
BS 著者版 Remark 2.37 の δ 押し出しの計算。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R]

private theorem torModule_subsingleton_of_elementwise_powerTorsion
    (a : R) (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (hM : IsCompletelyFlat (Ideal.span {a}) M) (hN : ∀ x : N, ∃ n : ℕ, a ^ n • x = 0)
    (i : ℕ) (hi : 0 < i) : Subsingleton (TorModule R i M N) := by
  let K (n : ℕ) : Submodule R N := LinearMap.ker ((a ^ n) • (LinearMap.id : N →ₗ[R] N))
  have hK {n m : ℕ} (h : n ≤ m) : K n ≤ K m := by
    intro x hx
    change a ^ n • x = 0 at hx
    change a ^ m • x = 0
    rw [← Nat.sub_add_cancel h, pow_add, mul_smul, hx, smul_zero]
  let F : ℕ ⥤ ModuleCat.{u} R :=
    { obj := fun n ↦ ModuleCat.of R (K n)
      map := fun f ↦ ModuleCat.ofHom (Submodule.inclusion (hK (leOfHom f))) }
  let c : Cocone F :=
    { pt := ModuleCat.of R N
      ι :=
        { app := fun n ↦ ModuleCat.ofHom (K n).subtype
          naturality := fun _ _ f ↦ by ext x; rfl } }
  let c₀ := ModuleCat.FilteredColimits.colimitCocone F
  let h₀ := ModuleCat.FilteredColimits.colimitCoconeIsColimit F
  let f := h₀.desc c
  have hf (n : ℕ) (x : K n) :
      f.hom (ModuleCat.FilteredColimits.M.mk F ⟨n, x⟩) = (x : N) :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (h₀.fac c n)) x
  have hb : Function.Bijective f.hom := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨n, x, rfl⟩ := ModuleCat.FilteredColimits.M.mk_surjective F y
      rw [hf] at hy
      have hx : x = 0 := Subtype.ext hy
      rw [hx]
      exact map_zero (c₀.ι.app n).hom
    · intro x
      obtain ⟨n, hn⟩ := hN x
      exact ⟨ModuleCat.FilteredColimits.M.mk F ⟨n, ⟨x, hn⟩⟩, hf n ⟨x, hn⟩⟩
  let e := (LinearEquiv.ofBijective f.hom hb).toModuleIso
  have hc : IsColimit c := h₀.ofIsoColimit (Cocone.ext e (h₀.fac c))
  let T := (Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R M)
  let := tor_preservesSequentialColimits (ModuleCat.of R M) i
  have ht := isColimitOfPreserves T hc
  apply ModuleCat.subsingleton_of_isZero
  apply (IsZero.iff_id_eq_zero _).mpr
  apply ht.hom_ext
  intro n
  have hKn : ∀ x : K n, a ^ n • x = 0 := fun x ↦ Subtype.ext x.property
  have hzero : Subsingleton ((F ⋙ T).obj n) :=
    torModule_subsingleton_of_completelyFlat_powerTorsion a M hM n (K n) hKn i hi
  exact (ModuleCat.isZero_of_subsingleton ((F ⋙ T).obj n)).eq_of_src _ _

/-- 概要：主元についての完全平坦性と局所化後の平坦性から高次 Tor が消える。
方針：局所化写像の冪ねじれ余核で Tor が消えることを短完全列に適用する。
規約：第二加群では主元の作用が単射。
使われ方：BS 著者版 Remark 2.37。 -/
theorem torModule_subsingleton_of_completelyFlat_of_localizedModule_flat
    (a : R) (M N L : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup L] [Module R L]
    (f : N →ₗ[R] L) [IsLocalizedModule (Submonoid.powers a) f]
    (hM : IsCompletelyFlat (Ideal.span {a}) M) (hN : IsSMulRegular N a)
    [Module.Flat R L] (i : ℕ) : Subsingleton (TorModule R (i + 1) M N) := by
  let Q := L ⧸ f.range
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers a) f).mp hx
    change a ^ n • x = 0 at hn
    exact hN.pow n (by simpa only [smul_zero] using hn)
  have hQ (x : Q) : ∃ n : ℕ, a ^ n • x = 0 := by
    obtain ⟨y, rfl⟩ := f.range.mkQ_surjective x
    obtain ⟨n, z, hz⟩ := IsLocalizedModule.Away.surj f a y
    refine ⟨n, ?_⟩
    rw [← map_smul, hz, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨z, rfl⟩
  have hQTor := torModule_subsingleton_of_elementwise_powerTorsion a M Q hM hQ (i + 2) (by omega)
  have hLTor (n : ℕ) : Subsingleton (TorModule R (n + 1) M L) := by
    have := torModule_subsingleton_of_flat (R := R) L M n
    exact (torModuleComm (n + 1) M L).injective.subsingleton
  obtain ⟨e⟩ := nonempty_torModule_succ_equiv M f f.range.mkQ hf f.range.mkQ_surjective
    f.exact_map_mkQ_range i (hLTor (i + 1)) (hLTor i)
  exact e.symm.injective.subsingleton

end SerrePositivity
