module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConnectiveCover
public import SerrePositivity.EInfinity.BarrattEccles.OperadStructure
public import SerrePositivity.EInfinity.BarrattEccles.Degrees

/-!
# 実 E 代数の smart connective cover

概要：任意可換環の実 E の非正次数性から、全代数の元の τ≤0 を代数化する。
方針：既存の正次数の零対象性を一般の切断構成へ代入する。
規約：元の包含を保ち、底が IsLE 0 なら同じ包含が擬同型となる。
使われ方：離散対象の本質像の逆包含。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A]

lemma arity_nonpositive (n : ℕ) : ((operad A).arity n).IsStrictlyLE 0 := by
  apply (CochainComplex.isStrictlyLE_iff _ 0).mpr
  intro i hi
  exact complex_isZero_positive A n i hi

def connectiveCover (B : (operad A).Algebra) : (operad A).Algebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.connectiveCover (arity_nonpositive A) B

def connectiveCoverInclusion (B : (operad A).Algebra) : connectiveCover A B ⟶ B :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.connectiveCoverInclusion (arity_nonpositive A) B

lemma connectiveCoverInclusion_quasiIso (B : (operad A).Algebra) [B.carrier.IsLE 0] :
    QuasiIso (connectiveCoverInclusion A B).hom := by
  change QuasiIso (B.carrier.ιTruncLE 0)
  exact (CochainComplex.quasiIso_ιTruncLE_iff B.carrier 0).mpr inferInstance

end SerrePositivity.EInfinity.BarrattEccles
