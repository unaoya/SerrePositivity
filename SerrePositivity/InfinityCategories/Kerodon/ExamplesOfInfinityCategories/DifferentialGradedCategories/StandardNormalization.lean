module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MooreSubmodule
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedEvaluation

/-!
# 標準 Hom の Mathlib 正規化の各項の比較

概要：Mathlib の正規化の項を具体的な正規化部分加群へ移し、最上位成分で単射に評価する。
方針：正の面の核を同定し、正規化された標準単体の一意性を使う。
規約：全射性と微分との両立は同型の完成に必要な残工程である。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の Mathlib Γ との同定。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：標準 Hom の Moore 正規化の各項は具体的な正規化部分加群と同型である。
方針：一般の単体的加群の正規化の同型に、標準の引き戻しによる核の同定を適用する。
規約：零次数も含む全ての次数。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の正規化複体の座標表示。 -/
def standardMooreTermIso (x y : D) (n : ℕ) :
    ((AlgebraicTopology.normalizedMooreComplex (ModuleCat.{u} R)).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).X n ≅
        ModuleCat.of R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizedSubmodule R x y n) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedModuleSubmodule (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y) n =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizedSubmodule R x y n := by
    cases n <;> rfl
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreNormalizedModuleIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y) n ≪≫
    eqToIso (congrArg (fun P : Submodule R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) ↦ ModuleCat.of R P) h)

/-- 概要：Moore 正規化の正次数の項を元の Hom の対応する負次数へ送る。
方針：具体的な正規化部分加群に移し、全体集合の成分で評価する。
規約：この時点では射の単射性を証明し、同型とは主張しない。
使われ方：HA 1.3.1.12 の正規化と切断 Hom の比較の各項。 -/
def standardMooreTopMap (x y : D) (n : ℕ) :
    ((AlgebraicTopology.normalizedMooreComplex (ModuleCat.{u} R)).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).X (n + 1) ⟶
        (homObject R D x y).X (-(n + 1 : ℤ)) :=
  (standardMooreTermIso (R := R) x y (n + 1)).hom ≫
    ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedTopEval (R := R) x y n)

/-- 概要：正次数の標準 Hom の Moore 正規化から負次数 Hom への評価射は単射である。
方針：具体的な正規化の評価の単射性と正規化の各項の同型を合成する。
規約：切断 Hom との同型性を前提にしていない。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の正規化複体の同定の単射性。 -/
lemma standardMooreTopMap_mono (x y : D) (n : ℕ) :
    Mono (standardMooreTopMap (R := R) x y n) := by
  have : Mono (ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedTopEval (R := R) x y n)) :=
    (ModuleCat.mono_iff_injective _).mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedTopEval_injective (R := R) x y n)
  dsimp only [standardMooreTopMap]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
