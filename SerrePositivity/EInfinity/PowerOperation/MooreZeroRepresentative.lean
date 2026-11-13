module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.ModulePiZeroMoore
public import SerrePositivity.EInfinity.ComplexLimits.DoldKanZeroIso

/-!
# 実 π₀/Moore 比較の零単体の代表元での計算

DAG XIII §2.2 の零次数の比較で使う一般の補助。元の opcycles 射と正規化包含を保持する。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory AlgebraicTopology HomologicalComplex
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable {A : Type u} [CommRing A]

/-- 二つの既存の零次数 Moore 同型は、同じ実包含から作られている。 -/
lemma mooreDegreeZeroIso_eq (W : SimplicialObject (ModuleCat A)) :
    moduleMooreDegreeZeroIso W = ComplexLimits.mooreDegreeZeroIso W := by
  apply Iso.ext
  rfl

/-- 同じ π₀/Moore 比較で零単体を写した値を、実ホモロジー射で計算する。 -/
lemma modulePiZeroMooreEquiv_mk (W : SimplicialObject (ModuleCat A))
    (x : W.obj (Opposite.op ⦋0⦌)) :
    modulePiZeroMooreEquiv W (SSet.π₀.mk x) =
      ((((normalizedMooreComplex (ModuleCat A)).obj W).pOpcycles 0) ≫
        ((normalizedMooreComplex (ModuleCat A)).obj W).isoHomologyι₀.inv).hom
          ((moduleMooreDegreeZeroIso W).inv.hom x) := by
  apply (ModuleCat.mono_iff_injective (moduleMooreZeroHomologyIso W).hom).mp inferInstance
  rw [modulePiZeroMooreEquiv_homologyBoundary]
  have h := congrArg (fun k => k.hom ((moduleMooreDegreeZeroIso W).inv.hom x))
    (moduleMooreZeroHomologyIso_pOpcycles W)
  change (moduleMooreZeroHomologyIso W).hom.hom
    (((((normalizedMooreComplex (ModuleCat A)).obj W).pOpcycles 0) ≫
      ((normalizedMooreComplex (ModuleCat A)).obj W).isoHomologyι₀.inv).hom
        ((moduleMooreDegreeZeroIso W).inv.hom x)) =
    Submodule.Quotient.mk ((moduleMooreDegreeZeroIso W).hom.hom
      ((moduleMooreDegreeZeroIso W).inv.hom x)) at h
  rw [Iso.inv_hom_id_apply] at h
  exact h.symm

end SerrePositivity.EInfinity.PowerOperation
