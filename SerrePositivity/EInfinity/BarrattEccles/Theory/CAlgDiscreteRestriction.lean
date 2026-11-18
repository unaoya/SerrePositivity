module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.DiscreteCoefficientOperations
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgCoefficientRestriction
public import SerrePositivity.EInfinity.BarrattEccles.CAlgDiscreteDerivedComparison

/-!
# 離散代数の CAlg への埋め込みと係数制限

## 概要
HA §3.2.2 の通常代数の係数制限は、CAlg の係数制限と自然に可換。

## 方針
元の厳密代数の比較を、全離散代数の自然同型に束ねて局所化する。

## 規約
界面の通常代数と同じ下圏の図式を使う。

## 使われ方
M13 の `discrete_restrict` 欄。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits SSet HomologicalComplex DifferentialGraded
open SerrePositivity.InfinityCategories
open scoped Simplicial

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

local notation "D" A => (underAlgFunctor A ⋙ discreteAlgebraFunctor A)

/-- 通常代数の係数制限と、厳密な離散 E 代数の係数制限の自然比較。 -/
def discreteAlgebraCoefficientRestrictionIso :
    restrictRingAlgebra f ⋙ (D S) ≅ (D T) ⋙ coefficientRestriction f := by
  refine NatIso.ofComponents (fun B =>
    cdgaCoefficientRestrictionIso f (discreteCoefficientMonoid T B)
      (discreteCoefficientMonoid S ((restrictRingAlgebra f).obj B))
      (discreteRestrictionCarrierIso f B) (discreteRestrictionMonoid_unit f B)
      (discreteRestrictionMonoid_mul f B)) ?_
  intro B C g
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
  apply HomologicalComplex.hom_ext
  intro i
  let M (B : RingAlgebra T) := ModuleCat.of S
    ((underAlgFunctor S).obj ((restrictRingAlgebra f).obj B))
  let N (B : RingAlgebra T) := ModuleCat.of T ((underAlgFunctor T).obj B)
  by_cases hi : i = 0
  · subst i
    let v := singleObjXSelf (.up ℤ) 0 (M B)
    apply (cancel_epi v.inv).mp
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let gₛ : M B ⟶ M C := ModuleCat.ofHom
      ((underAlgFunctor S).map ((restrictRingAlgebra f).map g)).hom.toLinearMap
    let gₜ : N B ⟶ N C := ModuleCat.ofHom ((underAlgFunctor T).map g).hom.toLinearMap
    change (discreteRestrictionCarrierIso f C).hom.f 0
        (((single (ModuleCat S) (.up ℤ) 0).map gₛ).f 0 (v.inv x)) =
      ((single (ModuleCat T) (.up ℤ) 0).map gₜ).f 0
        ((discreteRestrictionCarrierIso f B).hom.f 0 (v.inv x))
    rw [single_map_f_self, single_map_f_self]
    simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply, v, M, N]
    rfl
  · exact (isZero_single_obj_X (.up ℤ) 0 (M B) i hi).eq_of_src _ _

/-- 離散の埋め込みと導来係数制限は、全通常代数の図式上で可換。 -/
def barrattEcclesDiscrete_restrict :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap (restrictRingAlgebra f) ≫ discreteCAlgUnderEmbedding S)
      (discreteCAlgUnderEmbedding T ≫ barrattEcclesRestrict f) := by
  let η := discreteAlgebraCoefficientRestrictionIso f
  let e := algebraCAlgSourceNatTransIso S η.hom fun B => by
    change QuasiIso ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad S)).map (η.hom.app B))
    infer_instance
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (barrattEcclesRestrict_sourceIso f).symm (nerveMap (D T))
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e ≪≫ r) rfl (Category.assoc _ _ _).symm

end SerrePositivity.EInfinity.BarrattEccles
