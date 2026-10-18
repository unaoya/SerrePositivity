module

public import SerrePositivity.KST.ProExcision.IteratedQuotient
public import Mathlib.Algebra.Homology.SingleHomology

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# cone 長完全列による Koszul pro-消滅

概要：有限生成加群の正 Koszul ホモロジーの pro-消滅を反復 cone の比較から得る。
方針：係数を零次の一項複体に置き、負次数の通常商が零であることを使う。
規約：原典の正ホモロジー次数は本ファイルの負コホモロジー次数。
使われ方：KST Lemma 4.9。長完全列、冪核の安定化、対角の共終性による経路。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- 概要：零加群の反復通常冪商も各段で零。
方針：元の加群からの標準全射で任意の二元を比較する。
規約：スカラー列は任意。使われ方：KST Lemma 4.9 の負次数の比較の始域。 -/
theorem iteratedPowerQuotientTower_isZero_obj {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} R) (hM : IsZero M) (n : ℕ) :
    IsZero ((iteratedPowerQuotientTower z M).obj n) := by
  letI : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp hM
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := iteratedPowerQuotientProjection_surjective z M n x
  obtain ⟨b, rfl⟩ := iteratedPowerQuotientProjection_surjective z M n y
  have hab : (a : M) = (b : M) := Subsingleton.elim (α := M) a b
  exact congrArg ((iteratedPowerQuotientProjection z M).app n).hom hab

/-- 概要：有限加群を零次に置いた一項複体は各次数のホモロジーが有限。
方針：零次は係数への標準同型、他の次数は零性を使う。
規約：係数は有限生成。使われ方：KST Lemma 4.9 の Lemma 4.10 型比較への入力。 -/
theorem single_homology_finite (M : ModuleCat.{u} R) [Module.Finite R M] (i : ℤ) :
    Module.Finite R (((single (ModuleCat.{u} R) (.up ℤ) 0).obj M).homology i) := by
  by_cases hi : i = 0
  · subst i
    exact Module.Finite.equiv (singleObjHomologySelfIso (.up ℤ) 0 M).toLinearEquiv.symm
  · letI := ModuleCat.isZero_iff_subsingleton.mp
      (isZero_single_obj_homology (.up ℤ) 0 M i hi)
    infer_instance

/-- 概要：反復 cone の実冪遷移による有限加群の負次数 Koszul ホモロジーは pro-零。
方針：列長帰納法による比較の始域を零化し、pro 同型で終域へ移す。
規約：追加公理を用いず、有限性は係数加群上に要求する。
使われ方：KST Lemma 4.9 の cone 長完全列経路。 -/
theorem koszulConeModuleHomologyTower_isProZero [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (i : ℤ) (hi : i < 0) :
    IsProZero ((koszulConeTower z ((single (ModuleCat.{u} R) (.up ℤ) 0).obj M)).map
      (homologyFunctor _ _ i)) := by
  apply IsProZero.of_proIso (f := koszulConeComparison z _ i)
  · intro n
    refine ⟨n, le_refl n, ?_⟩
    exact (iteratedPowerQuotientTower_isZero_obj z _
      (isZero_single_obj_homology (.up ℤ) 0 M i (by omega)) n).eq_of_src _ _
  · exact koszulConeComparison_isProIso z _ (single_homology_finite M) i

end SerrePositivity.KST.ProExcision
