module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection

/-!
# 任意の複体の完備 Nakayama と完備化の検出

## 概要
主元完備な複体はスカラー錐で検出され、完備化の零性は元のスカラー錐へ戻せる。

## 方針
全次数のホモロジー加群の導来完備性と、完備化単位の Koszul 簡約を使う。

## 規約
BS 著者版 Proposition 6.2。複体の有界性・有限生成性は仮定しない。

## 使われ方
結晶被覆の完備底変換から二回の Nakayama で元の複体へ戻る。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- 概要：主元完備な任意の複体のホモロジーは同次数のスカラー錐で検出される。
方針：ホモロジー加群の完備性とスカラー作用の全射性から零性を得る。
規約：BS 著者版 Proposition 6.2。使われ方：p と d の完備 Nakayama。 -/
theorem cochain_homology_isZero_of_complete_of_scalarCone_isZero
    (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsComplete R a (DerivedCategory.Q.obj K)) (i : ℤ)
    (h : IsZero (((scalarConeFunctor a).obj K).homology i)) : IsZero (K.homology i) := by
  let e := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app K
  have hc := isModuleComplete_of_linearEquiv R a _ _ e.toLinearEquiv
    (isComplete_homology_isModuleComplete R a (DerivedCategory.Q.obj K) hK i)
  exact isZero_of_complete_of_smul_surjective a _ hc
    (cochain_homology_smul_surjective_of_scalarCone_isZero a K i h)

/-- 概要：完備化後が非輪状なら、元のスカラー錐も全次数で非輪状。
方針：完備化の単位の一乗 Koszul 簡約の擬同型と錐の長完全列を使う。
規約：BS 著者版 Proposition 6.2、非有界な主元完備化の実際の模型。
使われ方：完備底変換の零性から通常の剰余へ戻る。 -/
theorem scalarCone_homology_isZero_of_completion_acyclic
    (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : ∀ i : ℤ, IsZero (((complexCompletionFunctor R a).obj K).homology i)) (i : ℤ) :
    IsZero (((scalarConeFunctor a).obj K).homology i) := by
  let G (s : R) : Prop := QuasiIso ((scalarConeFunctor s).map (complexCompletionUnit R a K))
  have hq : G a := Eq.mp (congrArg G (pow_one a))
    (complexCompletionUnit_koszul_quasiIso R a K 1)
  letI : QuasiIso ((scalarConeFunctor a).map (complexCompletionUnit R a K)) := hq
  have hz := (Cone.exact₃ (smulId a ((complexCompletionFunctor R a).obj K))
    i (i + 1) rfl).isZero_of_both_isZero (h i) (h (i + 1))
  exact hz.of_iso (asIso (homologyMap
    ((scalarConeFunctor a).map (complexCompletionUnit R a K)) i))

/-- 概要：係数複体の主元完備性は、任意の有限 Koszul 複体で保たれる。
方針：反復錐の長さで帰納し、完備対象の拡大の閉性を使う。
規約：BS 著者版 Proposition 6.2。使われ方：各座標の Nakayama の入力。 -/
theorem koszulComplexOn_isComplete (a : R) {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsComplete R a (DerivedCategory.Q.obj K)) :
    IsComplete R a (DerivedCategory.Q.obj (koszulComplexOn x K)) := by
  induction r with
  | zero => exact hK
  | succ r ih =>
    exact isComplete_Q_mappingCone R a (smulId (x (Fin.last r))
      (koszulComplexOn (Fin.init x) K)) (ih (Fin.init x)) (ih (Fin.init x))

/-- 概要：全座標に完備な複体は有限 Koszul 簡約で検出される。
方針：末尾の座標の完備 Nakayama を適用して、列の長さで帰納する。
規約：BS 著者版 Proposition 6.2、正則性や有界性は不要。
使われ方：通常商への比較と忠実平坦な検出の後に元の複体へ戻る。 -/
theorem cochain_acyclic_of_complete_of_koszul_acyclic
    {r : ℕ} (x : Fin r → R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ j, IsComplete R (x j) (DerivedCategory.Q.obj K))
    (h : ∀ i : ℤ, IsZero ((koszulComplexOn x K).homology i)) :
    ∀ i : ℤ, IsZero (K.homology i) := by
  induction r with
  | zero => exact h
  | succ r ih =>
    apply ih (Fin.init x) (fun j => hK j.castSucc)
    intro i
    exact cochain_homology_isZero_of_complete_of_scalarCone_isZero
      (x (Fin.last r)) (koszulComplexOn (Fin.init x) K)
      (koszulComplexOn_isComplete (x (Fin.last r)) (Fin.init x) K (hK (Fin.last r))) i (h i)

/-- 概要：同じ主元で二回完備化した複体が非輪状なら、元のスカラー錐は非輪状。
方針：二回目の完備化の Koszul 比較と、一回目の単位の擬同型を使う。
規約：BS 著者版 Proposition 6.2、結晶的な二座標 (p,p) の完備化。
使われ方：原典の二座標完備底変換の実際の模型に適用する。 -/
theorem scalarCone_homology_isZero_of_repeated_completion_acyclic
    (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : ∀ i : ℤ, IsZero (((complexCompletionFunctor R a).obj
      ((complexCompletionFunctor R a).obj K)).homology i)) (i : ℤ) :
    IsZero (((scalarConeFunctor a).obj K).homology i) := by
  have hz := scalarCone_homology_isZero_of_completion_acyclic a
    ((complexCompletionFunctor R a).obj K) h i
  let G (s : R) : Prop := QuasiIso ((scalarConeFunctor s).map (complexCompletionUnit R a K))
  have hq : G a := Eq.mp (congrArg G (pow_one a))
    (complexCompletionUnit_koszul_quasiIso R a K 1)
  letI : QuasiIso ((scalarConeFunctor a).map (complexCompletionUnit R a K)) := hq
  exact hz.of_iso (asIso (homologyMap
    ((scalarConeFunctor a).map (complexCompletionUnit R a K)) i))

end SerrePositivity.DerivedCompletion
