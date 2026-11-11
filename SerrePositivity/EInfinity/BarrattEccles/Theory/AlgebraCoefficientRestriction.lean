module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientOperad
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientBraiding
public import SerrePositivity.EInfinity.BarrattEccles.Theory.AlgebraTransport
public import SerrePositivity.EInfinity.BarrattEccles.Fibrancy

/-!
# Barratt–Eccles 代数の厳密な係数制限

## 概要
HA §3.2.2 の係数制限を、Berger–Fresse §1.1 の厳密模型で構成する。

## 方針
オペラッドの係数写像と入力テンソルの比較を作用の前に合成する。

## 規約
底の複体を項別に係数制限し、零入力の演算を含める。

## 使われ方
M13 の導来係数制限と底変更随伴。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex HomotopicalAlgebra
open DifferentialGraded TensorPowers
open Functor.LaxMonoidal

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

attribute [local instance] scalarRestrictionLaxBraided

/-- オペラッドの係数写像は係数制限に沿う比較。 -/
def coefficientRestrictionComparison :
    Operad.LaxComparison (ScalarExtension.restriction f) (operad S) (operad T) where
  arity := coefficientComplexMap f
  permutation n σ := (coefficientSequenceMap f).naturality (FiniteBijection.permutation n σ)
  unit := coefficientComplexMap_unit f
  comp := coefficientComplexMap_partialComposition f

/-- 厳密代数の係数制限は、項別の係数制限を底に持つ関手。 -/
def coefficientRestriction : (operad T).Algebra ⥤ (operad S).Algebra :=
  Operad.transport (coefficientRestrictionComparison f)

/-- 係数制限は底の複体の擬同型を保つ。 -/
lemma coefficientRestriction_map_quasiIso {X Y : (operad T).Algebra} (g : X ⟶ Y)
    (hg : QuasiIso g.hom) : QuasiIso ((coefficientRestriction f).map g).hom := by
  change QuasiIso (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map g.hom)
  exact HomologicalComplex.quasiIso_map_of_preservesHomology _ _ (hφ := hg)

end SerrePositivity.EInfinity.BarrattEccles
