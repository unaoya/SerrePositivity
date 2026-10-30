module

public import SerrePositivity.HomologicalAlgebra.Complex.Truncation
public import SerrePositivity.CommutativeAlgebra.Koszul

/-! # Koszul 構成と切り詰めの局所的な比較

ある次数以上で項ごとに同型な射は、Koszul 構成後も同じ範囲で項ごとに同型である。
したがって、切り詰めの下端より上では、加法関手と Koszul 構成を施したホモロジーが一致する。
Koszul 列の長さに応じて切り詰めを余分に深くする必要はない。
-/

@[expose] public section

universe u v w

namespace SerrePositivity

open CategoryTheory Limits HomologicalComplex CochainComplex.mappingCone

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- 隣り合う二項で同型な射は、スカラー作用の錐のその次数でも同型となる。 -/
lemma scalarConeFunctor_map_f_isIso (x : R)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) (q : ℤ)
    [IsIso (f.f q)] [IsIso (f.f (q + 1))] :
    IsIso (((scalarConeFunctor x).map f).f q) := by
  have : IsIso (biprod.map (f.f (q + 1)) (f.f q)) :=
    (biprod.mapIso (asIso (f.f (q + 1))) (asIso (f.f q))).isIso_hom
  exact IsIso.of_isIso_fac_right (scalarConeFunctor_map_XIso x f q)

/-- 項ごとの同型が成立する上半直線は、Koszul 構成で保たれる。 -/
lemma koszulFunctor_map_f_isIso_above {e : ℕ} (x : Fin e → R)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) (a : ℤ)
    (hf : ∀ q, a ≤ q → IsIso (f.f q)) (q : ℤ) (hq : a ≤ q) :
    IsIso (((koszulFunctor x).map f).f q) := by
  induction e generalizing q with
  | zero => exact hf q hq
  | succ e ih =>
    have := ih (Fin.init x) q hq
    have := ih (Fin.init x) (q + 1) (by omega)
    exact scalarConeFunctor_map_f_isIso (x (Fin.last e)) ((koszulFunctor (Fin.init x)).map f) q

/-- 下端の一つ上からは、Koszul 構成後のホモロジーも同型となる。 -/
lemma koszulFunctor_map_quasiIsoAt_above {e : ℕ} (x : Fin e → R)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) (a : ℤ)
    (hf : ∀ q, a ≤ q → IsIso (f.f q)) (q : ℤ) (hq : a < q) :
    QuasiIsoAt ((koszulFunctor x).map f) q := by
  rw [quasiIsoAt_iff' _ (q - 1) q (q + 1) (by simp) (by simp)]
  let t := (shortComplexFunctor' (ModuleCat R) (.up ℤ) (q - 1) q (q + 1)).map
    ((koszulFunctor x).map f)
  have : IsIso t.τ₁ := koszulFunctor_map_f_isIso_above x f a hf (q - 1) (by omega)
  have : IsIso t.τ₂ := koszulFunctor_map_f_isIso_above x f a hf q (by omega)
  have : IsIso t.τ₃ := koszulFunctor_map_f_isIso_above x f a hf (q + 1) (by omega)
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono t

namespace StupidTruncation

variable {C : Type w} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  (F : C ⥤ ModuleCat.{u} R) [F.Additive]

/-- 加法関手と Koszul 構成を施しても、切り詰めの下端より上のホモロジーは保たれる。 -/
noncomputable def koszulMapHomologyIso {e : ℕ} (x : Fin e → R)
    (K : CochainComplex C ℤ) (a q : ℤ) (hq : a < q) :
    (koszulComplexOn x ((F.mapHomologicalComplex (.up ℤ)).obj (above K a))).homology q ≅
      (koszulComplexOn x ((F.mapHomologicalComplex (.up ℤ)).obj K)).homology q := by
  have hf (i : ℤ) (hi : a ≤ i) :
      IsIso (((F.mapHomologicalComplex (.up ℤ)).map (inclusion K a)).f i) := by
    have := inclusion_f_isIso K a i hi
    change IsIso (F.map ((inclusion K a).f i))
    infer_instance
  have := koszulFunctor_map_quasiIsoAt_above x
    ((F.mapHomologicalComplex (.up ℤ)).map (inclusion K a)) a hf q hq
  exact isoOfQuasiIsoAt
    ((koszulFunctor x).map ((F.mapHomologicalComplex (.up ℤ)).map (inclusion K a))) q

end StupidTruncation
end SerrePositivity
