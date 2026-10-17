module
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-! # 分裂包含に沿う追加微分の制限とchain map

## 概要
分裂包含に沿う追加微分の制限とchain map。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Preadditive HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {L K : Complex A}

lemma cochain_postcomp_injective_of_retraction (i : L ⟶ K) (r : K ⟶ L) (hir : i ≫ r = 𝟙 L)
    (T : Complex A) (p : ℤ) :
    Function.Injective (fun f : Cochain T L p => f.comp (Cochain.ofHom i) (add_zero p)) := by
  intro f g h
  have hh := congrArg (fun z : Cochain T K p => z.comp (Cochain.ofHom r) (add_zero p)) h
  simpa only [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
    hir, Cochain.comp_id] using hh

/-- 包含と追加微分の可換式から、制限した作用素の閉性を得る。 -/
lemma perturbation_closed_of_inclusion (i : L ⟶ K) (r : K ⟶ L) (hir : i ≫ r = 𝟙 L)
    (ψ : Cochain L L 1) (θ : Cochain K K 1) (hθ : δ 1 2 θ = 0)
    (hi : (Cochain.ofHom i).comp θ (zero_add 1) = ψ.comp (Cochain.ofHom i) (add_zero 1)) :
    δ 1 2 ψ = 0 := by
  apply cochain_postcomp_injective_of_retraction i r hir L 2
  dsimp only
  rw [Cochain.zero_comp, ← δ_comp_ofHom, ← hi, δ_ofHom_comp, hθ, Cochain.comp_zero]

/-- 同じ可換式から、制限した作用素の二乗零を得る。 -/
lemma perturbation_square_zero_of_inclusion (i : L ⟶ K) (r : K ⟶ L) (hir : i ≫ r = 𝟙 L)
    (ψ : Cochain L L 1) (θ : Cochain K K 1)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0)
    (hi : (Cochain.ofHom i).comp θ (zero_add 1) = ψ.comp (Cochain.ofHom i) (add_zero 1)) :
    ψ.comp ψ (show (1 : ℤ) + 1 = 2 by omega) = 0 := by
  apply cochain_postcomp_injective_of_retraction i r hir L 2
  dsimp only
  rw [Cochain.zero_comp, Cochain.comp_assoc_of_third_is_zero_cochain, ← hi,
    ← Cochain.comp_assoc_of_second_is_zero_cochain, ← hi,
    Cochain.comp_assoc_of_first_is_zero_cochain, hθθ, Cochain.comp_zero]

/-- 両側の微分変更と可換する元のchain map。 -/
def perturbMap (i : L ⟶ K) (ψ : Cochain L L 1) (θ : Cochain K K 1)
    (hψ : δ 1 2 ψ = 0) (hθ : δ 1 2 θ = 0)
    (hψψ : ψ.comp ψ (show (1 : ℤ) + 1 = 2 by omega) = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0)
    (hi : (Cochain.ofHom i).comp θ (zero_add 1) = ψ.comp (Cochain.ofHom i) (add_zero 1)) :
    perturbComplex L ψ hψ hψψ ⟶ perturbComplex K θ hθ hθθ :=
  CochainComplex.ofHom (fun n => i.f n) (fun n => by
    rw [perturbComplex_d, perturbComplex_d, comp_add, add_comp, i.comm]
    congr 1
    have h := congrArg (fun f : Cochain L K 1 => f.v n (n + 1) rfl) hi
    simpa only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v] using h)

lemma perturbMap_f (i : L ⟶ K) (ψ : Cochain L L 1) (θ : Cochain K K 1)
    (hψ : δ 1 2 ψ = 0) (hθ : δ 1 2 θ = 0)
    (hψψ : ψ.comp ψ (show (1 : ℤ) + 1 = 2 by omega) = 0)
    (hθθ : θ.comp θ (show (1 : ℤ) + 1 = 2 by omega) = 0)
    (hi : (Cochain.ofHom i).comp θ (zero_add 1) = ψ.comp (Cochain.ofHom i) (add_zero 1)) (n : ℤ) :
    (perturbMap i ψ θ hψ hθ hψψ hθθ hi).f n = i.f n := rfl

end SerrePositivity.DifferentialGraded
