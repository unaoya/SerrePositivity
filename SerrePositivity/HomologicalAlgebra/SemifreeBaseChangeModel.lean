module

public import SerrePositivity.HomologicalAlgebra.UnboundedSemifreeModel
public import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeComplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeKProjective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# 非有界な半自由分解上の底変換の不変性

## 概要
半自由模型間の擬同型は、任意の環射に沿う実際の係数拡大で保たれる。

## 方針
半自由性による K-projective 性から擬同型をホモトピー同値にし、加法的な係数拡大を通す。

## 規約
BS 著者版 Construction 6.1、Proposition 6.2。通常の非有界な複体のみを使う。

## 使われ方
存在する半自由分解、K-flat 性、テンソルとの実際の比較と合わせて、導来テンソルの模型を検証する。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory DifferentialGraded InfinityCategories
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 概要：任意の係数拡大は非有界な半自由模型間の擬同型を保つ。
方針：K-projective 複体間の擬同型をホモトピー同値として検出する。
規約：BS 著者版 Proposition 6.2、環射の平坦性は不要。
使われ方：実際の導来テンソルの模型の比較。 -/
theorem semifreeBaseChange_map_quasiIso (f : R →+* S)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (q : K ⟶ L) [QuasiIso q]
    (hK : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree R K) (hL : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree R L) :
    QuasiIso (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map q) := by
  letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_isKProjective R hK
  letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_isKProjective R hL
  have hh := (CochainComplex.IsKProjective.quasiIso_iff q).mp inferInstance
  exact homotopyEquivalences_le_quasiIso _ _ _
    ((ModuleCat.extendScalars f).homotopyEquivalences_mapHomologicalComplex_map q hh)

end SerrePositivity
