module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex

/-! # 比較 cochain の同型後合成による消去
概要：全整数次数の cochain は、標的の実鎖同型による後合成で区別できる。
方針：元の逆鎖写像を各次数で合成する。
規約：比較 cochain を零へ置き換えない。使われ方：gluing の代表加群比較の反映。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded

/-- 標的の同じ実鎖同型による後合成は、全次数の cochain に対して単射。 -/
lemma cochainPostIso_injective {R : Type u} [CommRing R] {K L T : Complex R}
    (e : L ≅ T) {n : ℤ} (a b : Cochain K L n)
    (h : a.comp (Cochain.ofHom e.hom) (add_zero n) =
      b.comp (Cochain.ofHom e.hom) (add_zero n)) : a = b := by
  apply Cochain.ext
  intro p q hpq
  have hv := Cochain.congr_v h p q hpq
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at hv
  have hh := congrArg (fun k => k ≫ e.inv.f q) hv
  simpa only [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
    HomologicalComplex.id_f, Category.comp_id] using hh

end SerrePositivity.KST.SConstruction
