module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CompletionAdditive
public import SerrePositivity.HomologicalAlgebra.CochainCompleteDetection
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-!
# 有限列についての既存の主元完備化の反復

## 概要
本体の主元完備化と標準単位を指定した列の順に反復する。

## 方針
別の冪の塔を選ばず、既存の関手の合成を使う。完備性の閉性は本体のものを使う。

## 規約
全座標の完備性と有限 Koszul の検出を明示する。単位の簡約の擬同型性は別途証明する。

## 使われ方
BS 著者版 Lemma 4.22 の有限生成イデアルの完備底変換。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- 他の主元で完備な複体の、元の主元完備化も同じ元で完備である。 -/
theorem completion_preserves_otherComplete (a b : R) (K : Complex R)
    (hK : IsComplete R b (DerivedCategory.Q.obj K)) :
    IsComplete R b (DerivedCategory.Q.obj ((complexCompletionFunctor R a).obj K)) :=
  isComplete_complexTowerHomotopyLimitObject_of_stages R b
    (complexPowerKoszulStage R a K) (complexPowerKoszulTransition R a K)
    (fun n => isComplete_Q_mappingCone R b (smulId (a ^ n) K) hK hK)

/-- 指定した有限列に沿う、既存の主元完備化関手の合成。 -/
def finiteCompletionFunctor : {r : ℕ} → (Fin r → R) → (Complex R ⥤ Complex R)
  | 0, _ => 𝟭 _
  | r+1, x => finiteCompletionFunctor (Fin.init x) ⋙ complexCompletionFunctor R (x (Fin.last r))

/-- 反復した関手は加法的である。 -/
instance finiteCompletionFunctor_additive {r : ℕ} (x : Fin r → R) :
    (finiteCompletionFunctor x).Additive := by
  induction r with
  | zero => change (𝟭 (Complex R)).Additive; infer_instance
  | succ r ih =>
    haveI := ih (Fin.init x)
    change (finiteCompletionFunctor (Fin.init x) ⋙
      complexCompletionFunctor R (x (Fin.last r))).Additive
    infer_instance

/-- 反復完備化の単位は、既存の標準単位だけの合成である。 -/
def finiteCompletionUnit : ∀ {r : ℕ} (x : Fin r → R) (K : Complex R),
    K ⟶ (finiteCompletionFunctor x).obj K
  | 0, _, K => 𝟙 K
  | r+1, x, K => finiteCompletionUnit (Fin.init x) K ≫
    complexCompletionUnit R (x (Fin.last r)) ((finiteCompletionFunctor (Fin.init x)).obj K)

/-- 元の標準単位の合成は、入力の複体について自然である。 -/
@[reassoc] theorem finiteCompletionUnit_naturality {r : ℕ} (x : Fin r → R)
    {K M : Complex R} (g : K ⟶ M) :
    g ≫ finiteCompletionUnit x M = finiteCompletionUnit x K ≫ (finiteCompletionFunctor x).map g := by
  induction r with
  | zero => simp [finiteCompletionUnit, finiteCompletionFunctor]
  | succ r ih =>
    change g ≫ (finiteCompletionUnit (Fin.init x) M ≫
      complexCompletionUnit R (x (Fin.last r)) ((finiteCompletionFunctor (Fin.init x)).obj M)) =
      (finiteCompletionUnit (Fin.init x) K ≫
        complexCompletionUnit R (x (Fin.last r)) ((finiteCompletionFunctor (Fin.init x)).obj K)) ≫
          (complexCompletionFunctor R (x (Fin.last r))).map ((finiteCompletionFunctor (Fin.init x)).map g)
    rw [← Category.assoc, ih (Fin.init x), Category.assoc, complexCompletionUnit_naturality]
    simp only [Category.assoc]

/-- 反復した関手は、元の非有界複体の擬同型を保つ。 -/
theorem finiteCompletionFunctor_map_quasiIso {r : ℕ} (x : Fin r → R)
    {K M : Complex R} (g : K ⟶ M) [QuasiIso g] :
    QuasiIso ((finiteCompletionFunctor x).map g) := by
  induction r with
  | zero => exact ‹QuasiIso g›
  | succ r ih =>
    haveI := ih (Fin.init x)
    exact complexCompletionFunctor_map_quasiIso R (x (Fin.last r))
      ((finiteCompletionFunctor (Fin.init x)).map g)

/-- 完備化後は、列の全ての元について完備である。 -/
theorem finiteCompletion_isComplete {r : ℕ} (x : Fin r → R) (K : Complex R) (j : Fin r) :
    IsComplete R (x j) (DerivedCategory.Q.obj ((finiteCompletionFunctor x).obj K)) := by
  induction r with
  | zero => exact Fin.elim0 j
  | succ r ih =>
    refine Fin.lastCases ?_ (fun k => ?_) j
    · exact complexCompletionObject_isComplete R (x (Fin.last r))
        ((finiteCompletionFunctor (Fin.init x)).obj K)
    · exact completion_preserves_otherComplete (x (Fin.last r)) (x k.castSucc)
        ((finiteCompletionFunctor (Fin.init x)).obj K) (ih (Fin.init x) k)

/-- 全座標に完備なら、同じ次数の有限 Koszul ホモロジーの零性で検出できる。 -/
theorem homology_isZero_of_finitelyComplete_koszul {r : ℕ} (x : Fin r → R) (K : Complex R)
    (hK : ∀ j, IsComplete R (x j) (DerivedCategory.Q.obj K)) (q : ℤ)
    (hq : IsZero ((koszulComplexOn x K).homology q)) : IsZero (K.homology q) := by
  induction r with
  | zero => exact hq
  | succ r ih =>
    apply ih (Fin.init x) (fun j => hK j.castSucc)
    exact cochain_homology_isZero_of_complete_of_scalarCone_isZero
      (x (Fin.last r)) (koszulComplexOn (Fin.init x) K)
      (koszulComplexOn_isComplete (x (Fin.last r)) (Fin.init x) K (hK (Fin.last r))) q hq

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
