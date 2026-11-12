module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.UniversalBoundaryCoefficients
/-!
概要：普遍 Hσ 係数は始点を保つ単体自己写像だけに支持される。
方針：有限面和表示の各基底ラベルを合成写像で判定し、零段・上方段を別に扱う。
規約：係数の非零支持を証明し、制限作用の自然性の仮定を省略しない。
使われ方：係数押出しと全 Hom の合成を交換する際の始点支持。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]

lemma dgCoherentBarUniversalComposite_basis_supported {l m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (hf : f.toOrderHom 0 = 0)
    (g : ⦋l⦌ ⟶ ⦋m⦌) (hg : g.toOrderHom 0 = 0) :
    ModuleCat.freeMk (R := R) (SSet.stdSimplex.objEquiv.symm (g ≫ f)) ∈
      Finsupp.supported R R {a : (Δ[n] : SSet.{u}) _⦋l⦌ | a 0 = 0} := by
  apply Finsupp.single_mem_supported R 1
  change f.toOrderHom (g.toOrderHom 0) = 0
  rw [hg, hf]

lemma dgCoherentBarUniversalBoundaryCoefficients_supported (n q : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalBoundaryCoefficients R n q ∈
      Finsupp.supported R R {a : (Δ[n] : SSet.{u}) _⦋n⦌ | a 0 = 0} := by
  let S := Finsupp.supported R R {a : (Δ[n] : SSet.{u}) _⦋n⦌ | a 0 = 0}
  change _ ∈ S
  cases n with
  | zero =>
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalBoundaryCoefficients_vertex]
    exact S.zero_mem
  | succ n =>
    by_cases hq : q ≤ n
    · let a := n - q
      have hn : n = a + q := by dsimp [a]; omega
      rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalBoundaryCoefficients_positive R hn]
      apply S.add_mem
      · apply S.sum_mem
        intro i _
        apply S.toAddSubgroup.zsmul_mem
        apply S.toAddSubgroup.zsmul_mem
        exact dgCoherentBarUniversalComposite_basis_supported R
          (SimplexCategory.σ ⟨a + 1, by omega⟩) (by
            simp [SimplexCategory.σ, Fin.predAboveOrderHom])
          (SimplexCategory.δ i.succ) (by
            simp [SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.succAbove])
      · apply S.sum_mem
        intro i _
        apply S.toAddSubgroup.zsmul_mem
        apply S.toAddSubgroup.zsmul_mem
        exact dgCoherentBarUniversalComposite_basis_supported R
          (SimplexCategory.δ i.succ) (by
            simp [SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.succAbove])
          (SimplexCategory.σ ⟨a, by omega⟩) (by
            simp [SimplexCategory.σ, Fin.predAboveOrderHom])
    · by_cases hlast : q = n + 1
      · subst q
        rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalBoundaryCoefficients_last]
        apply S.sum_mem
        intro i _
        apply S.toAddSubgroup.zsmul_mem
        exact dgCoherentBarUniversalComposite_basis_supported R
          (SimplexCategory.σ (0 : Fin (n + 2))) (by
            simp [SimplexCategory.σ, Fin.predAboveOrderHom])
          (SimplexCategory.δ i.succ.succ) (by
            simp [SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.succAbove])
      · rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalBoundaryCoefficients_above R (by omega)]
        exact S.zero_mem

lemma dgCoherentBarUniversalBoundaryCoefficients_based (n q : ℕ)
    (a : (Δ[n] : SSet.{u}) _⦋n⦌) (ha : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarUniversalBoundaryCoefficients R n q a ≠ 0) :
    a 0 = 0 :=
  (Finsupp.mem_supported R _).1 (dgCoherentBarUniversalBoundaryCoefficients_supported R n q)
    (Finsupp.mem_support_iff.mpr ha)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
