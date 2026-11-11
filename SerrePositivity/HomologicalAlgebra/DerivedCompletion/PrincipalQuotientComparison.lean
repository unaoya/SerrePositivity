module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FiniteQuotientComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionLinearMap
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 関係商と実主元完備化の比較

## 概要
完備化後の関係商が導来 p 完備なら、元の関係商の実 H⁰ 完備化と単位を保って環同型になる。
## 方針
両方向の環射を実完備化の普遍性から作り、商と完備化の一意性で両逆を確認する。
## 規約
BS 著者版 Proposition 7.10 の有限 T。完備性の入力は有限関係商の場合に別途供給する。
## 使われ方
生の関係商の有界ねじれを、完備な根付き基底の通常商へ移す。
-/

public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (p : ℕ) (I : Ideal R)
local notation "H" => CompletedRing p R
local notation "j" => CommRingCat.Hom.hom (principalCompletionRingCatUnit p (CommRingCat.of R))
local notation "T" => H ⧸ Ideal.map j I
local notation "q" => Ideal.Quotient.mk I
local notation "qH" => Ideal.Quotient.mk (Ideal.map j I)
local notation "s" => Ideal.quotientMap (Ideal.map j I) j Ideal.le_comap_map
local notation "D" => CompletedRing p (R ⧸ I)
local notation "u" => CommRingCat.Hom.hom (principalCompletionRingCatUnit p (CommRingCat.of (R ⧸ I)))

/-- 概要：導来完備な関係商は、元の関係商の実 H⁰ 完備化と単位を保って同型。
方針：二つの普遍性から両方向の射を作り、一意性で両逆を示す。
規約：BS 著者版 Proposition 7.10。p 正則性・Noether 性は不要。
使われ方：有限 T の二つの完備化の定義を比較する。 -/
theorem exists_principalCompletionQuotientEquiv_of_complete
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T)) :
    ∃ e : T ≃+* D, e.toRingHom.comp s = u := by
  let g : H →+* D := principalCompletionMap q (p : R) (p : R ⧸ I) (map_natCast q p)
  have hg : g.comp j = (u).comp q := principalCompletionMap_comp q (p : R) (p : R ⧸ I) (map_natCast q p)
  have hI : Ideal.map j I ≤ RingHom.ker g := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change (g.comp j) x = 0
    rw [hg]
    change u (q x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  let b : T →+* D := Ideal.Quotient.lift _ g hI
  have hb : b.comp s = u := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    change g (j x) = u (q x)
    exact RingHom.congr_fun hg x
  have hTs : letI := (s).toAlgebra; letI : Module (R ⧸ I) T := Algebra.toModule;
      IsModuleComplete (R ⧸ I) (p : R ⧸ I) (ModuleCat.of (R ⧸ I) T) := by
    letI := (s).toAlgebra
    letI : Module (R ⧸ I) T := Algebra.toModule
    apply (isModuleComplete_algebraMap_iff (R ⧸ I) T (p : R ⧸ I) T).mp
    simpa only [map_natCast] using hT
  obtain ⟨a₀, ha₀, _⟩ := principalCompletion_existsUnique_ringHom (R ⧸ I) (p : R ⧸ I) T s hTs
  let a : D →+* T := a₀
  have ha : a.comp u = s := ha₀
  have hD := principalCompletion_isModuleComplete_unit (R := R ⧸ I) (p : R ⧸ I)
  have hab : b.comp a = RingHom.id D := by
    apply (principalCompletion_existsUnique_ringHom (R ⧸ I) (p : R ⧸ I) D u hD).unique
    · apply RingHom.ext
      intro x
      exact (congrArg b (RingHom.congr_fun ha x)).trans (RingHom.congr_fun hb x)
    · exact RingHom.id_comp u
  have hTr : letI := ((qH).comp j).toAlgebra; letI : Module R T := Algebra.toModule;
      IsModuleComplete R (p : R) (ModuleCat.of R T) := by
    letI := ((qH).comp j).toAlgebra
    letI : Module R T := Algebra.toModule
    apply (isModuleComplete_algebraMap_iff R T (p : R) T).mp
    simpa only [map_natCast] using hT
  have hba : a.comp b = RingHom.id T := by
    apply Ideal.Quotient.ringHom_ext
    apply (principalCompletion_existsUnique_ringHom R (p : R) T ((qH).comp j) hTr).unique
    · apply RingHom.ext
      intro x
      change a (g (j x)) = qH (j x)
      have hgj : g (j x) = u (q x) := RingHom.congr_fun hg x
      rw [hgj]
      change (a.comp u) (q x) = qH (j x)
      rw [ha]
      rfl
    · rfl
  exact ⟨RingEquiv.ofRingHom b a hab hba, hb⟩

end SerrePositivity.DerivedCompletion
