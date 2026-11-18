module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaComponents
public import SerrePositivity.EInfinity.PowerOperation.MooreZeroRepresentative
public import SerrePositivity.EInfinity.PowerOperation.ChainZeroClassNaturality

/-!
# Γ の成分比較の実零単体での計算

DAG XIII §2.2 の Ω 比較への前段。同じ Γ の零次数同型と正規化余単位の
射への作用を保持し、連結成分の代表を smart 切断のホモロジー類へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory AlgebraicTopology HomologicalComplex
open scoped Simplicial
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A]

lemma gammaPiZeroTruncationEquiv_mk (M : Complex A)
    (x : (gammaModule A M).obj (Opposite.op ⦋0⦌)) :
    gammaPiZeroTruncationEquiv A M (SSet.π₀.mk x) =
      (chainZeroClass (M.truncLE' (ComplexShape.embeddingUpIntLE 0))).hom
        ((_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso
          (M.truncLE' (ComplexShape.embeddingUpIntLE 0))).hom.hom x) := by
  let L := M.truncLE' (ComplexShape.embeddingUpIntLE 0)
  let W := gammaModule A M
  let c := (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
    ChainComplex (ModuleCat A) ℕ).counitIso.app L
  change (homologyMap c.hom 0).hom
    (modulePiZeroMooreEquiv W (SSet.π₀.mk x)) = _
  rw [modulePiZeroMooreEquiv_mk]
  have h := congrArg (fun k => k.hom ((moduleMooreDegreeZeroIso W).inv.hom x))
    (chainZeroClass_naturality c.hom)
  change (homologyMap c.hom 0).hom
    ((chainZeroClass ((normalizedMooreComplex (ModuleCat A)).obj W)).hom
      ((moduleMooreDegreeZeroIso W).inv.hom x)) =
    (chainZeroClass L).hom (c.hom.f 0 ((moduleMooreDegreeZeroIso W).inv.hom x)) at h
  rw [mooreDegreeZeroIso_eq] at h
  rw [mooreDegreeZeroIso_eq]
  change (homologyMap c.hom 0).hom
    ((chainZeroClass ((normalizedMooreComplex (ModuleCat A)).obj W)).hom
      ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso W).inv.hom x)) =
    (chainZeroClass L).hom (c.hom.f 0 ((_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso W).inv.hom x))
  exact h

end SerrePositivity.EInfinity.PowerOperation
