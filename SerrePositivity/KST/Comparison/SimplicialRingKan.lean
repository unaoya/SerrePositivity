module

public import SerrePositivity.KST.Comparison.RingHornUpper
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# 単体的環の台単体集合は Kan である

概要：任意の単体的環のホーンを加法と退化で充填する。
方針：次元一は完全退化で充填し、それ以上は低い面からと高い面からの有限補正を使う。
規約：KST Lemma 2.13 の単体的加法群の Kan 性を直接構成する証明経路。
使われ方：ĜL の正次数の群の比較から未証明の Kan 性の仮定を除く。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped Simplicial

/--
概要：単体的環の台単体集合は全てのホーンを充填する Kan 複体である。
方針：一次元のホーンは退化で充填し、それ以上は互換な面の有限回の補正を適用する。
規約：単体的環の乗法逆元・可換性・connective 性に関する追加入力は不要。
使われ方：KST Lemma 2.13 の有限 rank の高次の行列公式。
-/
instance ringSpace_kanComplex (A : SimplicialObject RingCat.{u}) : KanComplex (ringSpace A) := by
  rw [KanComplex.iff]
  intro n k f hf
  cases n with
  | zero =>
    fin_cases k
    · let a : A.obj (op ⦋0⦌) := yonedaEquiv (f 1 (by decide))
      refine ⟨yonedaEquiv.symm ((A.σ (0 : Fin 1)).hom a), fun j hj => ?_⟩
      fin_cases j
      · exact False.elim (hj rfl)
      · apply yonedaEquiv.injective
        rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
        exact congrArg (fun q => q.hom a) (A.δ_comp_σ_succ (i := (0 : Fin 1)))
    · let a : A.obj (op ⦋0⦌) := yonedaEquiv (f 0 (by decide))
      refine ⟨yonedaEquiv.symm ((A.σ (0 : Fin 1)).hom a), fun j hj => ?_⟩
      fin_cases j
      · apply yonedaEquiv.injective
        rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
        exact congrArg (fun q => q.hom a) (A.δ_comp_σ_self (i := (0 : Fin 1)))
      · exact False.elim (hj rfl)
  | succ n =>
    let F := RingHornFaces.ofCompatible A f hf
    obtain ⟨y, hy⟩ := F.exists_filler A
    refine ⟨yonedaEquiv.symm y, fun j hj => ?_⟩
    apply yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    exact hy j hj

end SerrePositivity.KST.Comparison
