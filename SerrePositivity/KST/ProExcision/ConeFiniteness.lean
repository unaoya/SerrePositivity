module

public import SerrePositivity.KST.ProExcision.ScalarConePro
public import Mathlib.RingTheory.Finiteness.Finsupp

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# 反復 cone のホモロジーの有限性

概要：係数複体の項の有限性を仮定せず、ホモロジーの有限性を Koszul 構成へ移す。
方針：cone 長完全列の連結写像の像へ標的を制限し、有限加群の拡張を使う。
規約：基底環は Noether。複体は有界でなくてもよい。
使われ方：KST Lemma 4.10 の列長帰納法での冪核の消滅指数の存在。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- 概要：隣接する二つのホモロジーが有限なら、スカラー cone の当該ホモロジーは有限。
方針：長完全列を連結射の像で切り、有限生成加群の拡張へ帰着する。
規約：係数複体の項に有限性を要求しない。
使われ方：KST Lemma 4.10 の一変数比較の反復。 -/
theorem scalarCone_homology_finite (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    [Module.Finite R (K.homology i)] [Module.Finite R (K.homology (i + 1))] :
    Module.Finite R (((scalarConeFunctor a).obj K).homology i) := by
  let f := (homologyMap (CochainComplex.mappingCone.inr (smulId a K)) i).hom
  let g := (Cone.δ (smulId a K) i (i + 1) rfl).hom
  have hex : Function.Exact f g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (Cone.exact₃ (smulId a K) i (i + 1) rfl)
  have hex' : Function.Exact f g.rangeRestrict := by
    intro x
    change (⟨g x, _⟩ : LinearMap.range g) = 0 ↔ _
    rw [Subtype.ext_iff]
    exact hex x
  apply Module.Finite.of_exact hex'
  rintro ⟨_, x, rfl⟩
  exact ⟨x, rfl⟩

/-- 概要：ホモロジーが有限な複体上の反復 Koszul cone もホモロジーが有限。
方針：列長について帰納し、各段の cone 長完全列を使う。
規約：次数ごとの有限性だけを要求。使われ方：KST Lemma 4.10 の冪指数の独立な帰納法。 -/
theorem koszulComplexOn_homology_finite : ∀ {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ i, Module.Finite R (K.homology i)) (i : ℤ),
    Module.Finite R ((koszulComplexOn z K).homology i)
  | 0, _, K, hK, i => hK i
  | e + 1, z, K, hK, i => by
      let := koszulComplexOn_homology_finite (Fin.init z) K hK i
      let := koszulComplexOn_homology_finite (Fin.init z) K hK (i + 1)
      exact scalarCone_homology_finite (z (Fin.last e)) (koszulComplexOn (Fin.init z) K) i

end SerrePositivity.KST.ProExcision
