module

public import SerrePositivity.HomologicalAlgebra.ConeLES
public import SerrePositivity.HomologicalAlgebra.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# 持ち上げの写像錐は余核の分解

## 概要

`A` 加群の短完全列 `0 → V₁ →f V₂ →g V₃ → 0` が与えられたとき、`V₁`、`V₂` の射影分解の間に `f` を
持ち上げた鎖写像 `f̃` をとり、その写像錐 `Cone f̃` を考えると、これは `V₃` の分解になる
（`isResolutionOf_cone`）。これは馬蹄補題（三つの分解を同時にとる）の代わりになる構成で、
Tor の長完全列（`TorLES.lean`）を写像錐の長完全列から出すために使う。分解はすべて ℤ 添字の
cochain 複体に延長した形（`Resolution.lean` の `extRes`）で扱う。

## 証明の筋道

`Cone f̃` が `IsResolutionOf (Cone f̃) V₃` の四つの条件をみたすことを確かめる。

- 正の次数で零、各項は射影的：写像錐の項は `resV V₁` の項と `resV V₂` の項の直和だから。
- `H^i(Cone f̃) = 0 (i ≠ 0)`：写像錐の長完全列（`ConeLES.lean`）
  `H^i(resV V₁) → H^i(resV V₂) → H^i(Cone f̃) → H^{i+1}(resV V₁)` で、`i ≠ 0, -1` では両端が零。
  `i = -1` では `H^{-1}(Cone f̃) →δ H^0(resV V₁) → H^0(resV V₂)` の第二の射が `f` に対応して
  単射なので連結射 `δ` は零、一方 `H^{-1}(resV V₂) = 0` から `δ` は単射、よって `H^{-1}(Cone f̃) = 0`。
- `H^0(Cone f̃) ≅ V₃`：長完全列から `H^0(Cone f̃) ≅ coker(H^0 f̃) ≅ coker f`、短完全列の完全性と
  `g` の全射性から `coker f ≅ V₃`（`coneHomologyZeroEquiv`）。

`H^0(f̃)` が `f` に対応すること（`homologyMap_liftSES_zero`）は `extLift_homologyZero` による。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable (A : Type u) [CommRing A]

/-- `A` 加群 `V` の射影分解（Mathlib の `projectiveResolution` で選んだもの）を ℤ 添字 cochain 複体に
延長したもの。`-n` 次の項が分解の `n` 番目の射影加群で、正の次数は零。 -/
noncomputable abbrev resV (V : Type u) [AddCommGroup V] [Module A V] :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  extRes (projectiveResolution (ModuleCat.of A V))

/-- `resV V` の `0` 次ホモロジーと `V` の同型（`extResHomologyZeroIso`）。長完全列の `0` 次の部分を
`V` の言葉に書き直すのに使う。 -/
noncomputable abbrev resVHomologyZeroIso (V : Type u) [AddCommGroup V] [Module A V] :
    (resV A V).homology 0 ≅ ModuleCat.of A V :=
  extResHomologyZeroIso (projectiveResolution (ModuleCat.of A V))

variable {A}
variable {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [Module A V₁] [AddCommGroup V₂] [Module A V₂]
  [AddCommGroup V₃] [Module A V₃]

/-- 線形写像 `f : V₁ → V₂` の、分解の間の鎖写像 `f̃ : resV V₁ ⟶ resV V₂` への持ち上げ（`extLift`）。
`0` 次のホモロジーで `f` を誘導する。この写像錐が `V₃` の分解になる。 -/
noncomputable abbrev liftSES (f : V₁ →ₗ[A] V₂) : resV A V₁ ⟶ resV A V₂ :=
  extLift (projectiveResolution (ModuleCat.of A V₁)) (ModuleCat.ofHom f)
    (projectiveResolution (ModuleCat.of A V₂))

/-- 持ち上げ `f̃` が `0` 次ホモロジーに誘導する射は、同一視 `resVHomologyZeroIso` のもとで `f` そのもの
である。`extLift_homologyZero` を同型で移項した形。 -/
lemma homologyMap_liftSES_zero (f : V₁ →ₗ[A] V₂) :
    HomologicalComplex.homologyMap (liftSES f) 0 =
      (resVHomologyZeroIso A V₁).hom ≫ ModuleCat.ofHom f ≫ (resVHomologyZeroIso A V₂).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact extLift_homologyZero _ _ _

variable (f : V₁ →ₗ[A] V₂) (g : V₂ →ₗ[A] V₃)

/-- `f` が単射なら、`H^0(f̃)` は単射（mono）である。`homologyMap_liftSES_zero` で `f` に書き直し、
単射な線形写像は `ModuleCat` の mono であることによる。`H^{-1}(Cone f̃) = 0` の証明で、連結射が
零になることを示すのに使う。 -/
lemma mono_homologyMap_liftSES_zero (hf : Function.Injective f) :
    Mono (HomologicalComplex.homologyMap (liftSES f) 0) := by
  rw [homologyMap_liftSES_zero]
  have : Mono (ModuleCat.ofHom f) := (ModuleCat.mono_iff_injective _).mpr hf
  infer_instance

/-- 短完全列 `0 → V₁ →f V₂ →g V₃ → 0` について、`H^0(Cone f̃) ≃ V₃`。長完全列
`H^0(resV V₁) → H^0(resV V₂) → H^0(Cone f̃) → H^1(resV V₁) = 0` から、`H^0(Cone f̃)` は `H^0(f̃)` の
余核である。`H^0(f̃)` は同一視のもとで `f` なので余核は `V₂ / im f`、完全性 `im f = ker g` と `g` の
全射性から `V₂ / ker g ≅ V₃`。これらの同型を順につないで構成する。 -/
noncomputable def coneHomologyZeroEquiv (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    (Cone.cone (liftSES f)).homology 0 ≃ₗ[A] V₃ := by
  have h2 := Cone.exact₂ (liftSES f) 0
  have h3 := Cone.exact₃ (liftSES f) 0 1 rfl
  have hepi : Epi (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr (liftSES f)) 0) :=
    h3.epi_f ((extRes_isZero_homology _ 1 one_ne_zero).eq_zero_of_tgt _)
  have hsurj : Function.Surjective
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr (liftSES f)) 0).hom :=
    (ModuleCat.epi_iff_surjective _).mp hepi
  have hrk : LinearMap.range (HomologicalComplex.homologyMap (liftSES f) 0).hom =
      LinearMap.ker (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (liftSES f)) 0).hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h2
  let e₁ := (resVHomologyZeroIso A V₁).toLinearEquiv
  let e₂ := (resVHomologyZeroIso A V₂).toLinearEquiv
  -- `range (H^0 f̃)` を `e₂` で移すと `range f`
  have hmap : (LinearMap.range (HomologicalComplex.homologyMap (liftSES f) 0).hom).map
      (e₂ : (resV A V₂).homology 0 →ₗ[A] V₂) = LinearMap.range f := by
    rw [← LinearMap.range_comp, homologyMap_liftSES_zero]
    have : (e₂ : (resV A V₂).homology 0 →ₗ[A] V₂) ∘ₗ
        ((resVHomologyZeroIso A V₁).hom ≫ ModuleCat.ofHom f ≫
          (resVHomologyZeroIso A V₂).inv).hom =
        f ∘ₗ (e₁ : (resV A V₁).homology 0 →ₗ[A] V₁) := by
      ext y
      simp [e₁, e₂]
    rw [this, LinearMap.range_comp_of_range_eq_top _ e₁.range]
  exact (LinearMap.quotKerEquivOfSurjective _ hsurj).symm.trans
    ((Submodule.quotEquivOfEq _ _ hrk.symm).trans
      ((Submodule.Quotient.equiv _ _ e₂ hmap).trans
        ((Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp hfg).symm).trans
          (LinearMap.quotKerEquivOfSurjective g hg))))

/-- **持ち上げの錐は余核の分解**：短完全列 `0 → V₁ →f V₂ →g V₃ → 0` について、`Cone f̃` は `V₃` の
分解である。正の次数で零であることと射影性は項が直和であることから、ホモロジーの消滅は写像錐の
長完全列から（`i = -1` では `H^0(f̃)` の単射性を使って連結射が零になる）、`H^0 ≅ V₃` は
`coneHomologyZeroEquiv` による。 -/
noncomputable def isResolutionOf_cone (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    IsResolutionOf (Cone.cone (liftSES f)) (ModuleCat.of A V₃) where
  isZero_X i hi := by
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨extRes_isZero_X _ _ (by omega), extRes_isZero_X _ _ hi⟩
  projective i := by
    have := extRes_projective (projectiveResolution (ModuleCat.of A V₁)) (i + 1)
    have := extRes_projective (projectiveResolution (ModuleCat.of A V₂)) i
    exact Projective.of_iso
      (HomologicalComplex.homotopyCofiber.XIsoBiprod (liftSES f) i (i + 1) rfl).symm
      inferInstance
  isZero_homology i hi := by
    by_cases hi1 : i = -1
    · subst hi1
      have h10 : (-1 : ℤ) + 1 = 0 := by norm_num
      have h3 := Cone.exact₃ (liftSES f) (-1) 0 h10
      have hz : IsZero ((resV A V₂).homology (-1)) := extRes_isZero_homology _ (-1) (by norm_num)
      have hmonoδ : Mono (Cone.δ (liftSES f) (-1) 0 h10) := h3.mono_g (hz.eq_zero_of_src _)
      have hcomp : Cone.δ (liftSES f) (-1) 0 h10 ≫
          HomologicalComplex.homologyMap (liftSES f) 0 = 0 :=
        comp_eq_zero_transport (Cone.S₁ (liftSES f) (-1) 0 h10) _ _ _ _ _
          (Cone.δ_square (liftSES f) (-1) 0 h10) (Cone.e_naturality 0 (liftSES f))
      have := mono_homologyMap_liftSES_zero f hf
      have hδ : Cone.δ (liftSES f) (-1) 0 h10 = 0 := zero_of_comp_mono _ hcomp
      rw [IsZero.iff_id_eq_zero, ← cancel_mono (Cone.δ (liftSES f) (-1) 0 h10), Category.id_comp,
        zero_comp, hδ]
    · exact (Cone.exact₃ (liftSES f) i (i + 1) rfl).isZero_of_both_isZero
        (extRes_isZero_homology _ i hi) (extRes_isZero_homology _ (i + 1) (by omega))
  homologyZeroIso := (coneHomologyZeroEquiv f g hg hfg).toModuleIso

end SerrePositivity
