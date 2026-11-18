module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientMonoidAction
public import SerrePositivity.EInfinity.BarrattEccles.DiscreteAlgebra
public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.SinglePairingValue
public import SerrePositivity.EInfinity.Interface.Theory

/-!
# 離散代数の係数制限と零次埋め込み

## 概要
HA §3.2.2 の離散代数の係数制限は、零次埋め込みの単位と積を保つ。

## 方針
同じ元を送る零次の比較同型を作り、単位と純粋テンソル上で照合する。

## 規約
元の通常代数を `RingAlgebra` の下圏表示で取る。

## 使われ方
M13 の `discrete_restrict` 欄。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded
open Functor.LaxMonoidal
open scoped TensorProduct

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

local notation "R" => ScalarExtension.restriction
/-- 下圏表示の通常代数を可換代数の圏へ戻す。 -/
abbrev underAlgFunctor (A : Type u) [CommRing A] : RingAlgebra A ⥤ CommAlgCat A :=
  (commAlgCatEquivUnder (CommRingCat.of A)).inverse

/-- 下圏で制限した通常代数の底の加群と、加群の係数制限の自然な比較。 -/
def discreteRestrictionModuleIso (B : RingAlgebra T) :
    ModuleCat.of S ((underAlgFunctor S).obj ((restrictRingAlgebra f).obj B)) ≅
      (ModuleCat.restrictScalars f).obj (ModuleCat.of T ((underAlgFunctor T).obj B)) := by
  let Bₛ := (underAlgFunctor S).obj ((restrictRingAlgebra f).obj B)
  let Bₜ := (underAlgFunctor T).obj B
  let M := ModuleCat.of S Bₛ
  let N := (ModuleCat.restrictScalars f).obj (ModuleCat.of T Bₜ)
  let e : M ≃ₗ[S] N := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun a x => by
      let x' : Bₜ := x
      have hS : (a • (x : Bₛ)) = algebraMap S Bₛ a * x := Algebra.smul_def a x
      have hT : (f a • x') = algebraMap T Bₜ (f a) * x' := Algebra.smul_def (f a) x'
      exact hS.trans hT.symm }
  exact e.toModuleIso

/-- 係数制限と零次埋め込みの比較。 -/
def discreteRestrictionCarrierIso (B : RingAlgebra T) :
    cochainSingleZero (ModuleCat.of S ((underAlgFunctor S).obj ((restrictRingAlgebra f).obj B))) ≅
      (R f).obj (cochainSingleZero (ModuleCat.of T ((underAlgFunctor T).obj B))) :=
  (CochainComplex.singleFunctor (ModuleCat S) 0).mapIso (discreteRestrictionModuleIso f B) ≪≫
    ((singleMapHomologicalComplex (ModuleCat.restrictScalars f) (.up ℤ) 0).app
      (ModuleCat.of T ((underAlgFunctor T).obj B))).symm

/-- 零次での比較は通常代数の元を保つ。 -/
lemma discreteRestrictionCarrierIso_zero (B : RingAlgebra T) (x : (underAlgFunctor T).obj B) :
    ((discreteRestrictionCarrierIso f B).hom.f 0)
      ((singleObjXSelf (.up ℤ) 0
        (ModuleCat.of S ((underAlgFunctor S).obj ((restrictRingAlgebra f).obj B)))).inv x) =
    (singleObjXSelf (.up ℤ) 0 (ModuleCat.of T ((underAlgFunctor T).obj B))).inv x := by
  simp only [discreteRestrictionCarrierIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    HomologicalComplex.comp_f,
    CochainComplex.singleFunctor, single_map_f_self, ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
