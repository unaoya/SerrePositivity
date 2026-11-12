module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedLiftEquation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardNormalization

/-!
# 標準 Hom の正規化の正次数の線形同値

概要：最上位成分による正規化の評価は正次数で線形同値となる。
方針：二成分の持ち上げの正の面が消えることを証明して全射性を得る。
規約：この各項の同型だけでは複体の同型を主張しない。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の切断 Hom との比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：二成分の持ち上げは全ての正の面が零であり正規化されている。
方針：正の面の像が対応する正の頂点を欠くため支持点を含まないことを使う。
規約：標準単体の方程式は既に証明したものを使う。
使われ方：HA 1.3.1.12 の正規化の評価の全射性。 -/
lemma normalizedLift_mem {n : ℕ} (z : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y (-(n + 1 : ℤ))) :
    (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedLiftData z, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedLiftData_mem_standard z⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y (n + 1))
      ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizedSubmodule R x y (n + 1) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_standardNormalizedSubmodule_iff _).mpr
  intro j
  apply Subtype.ext
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_val]
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback (SimplexCategory.δ j.succ).toOrderHom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedLiftData z)).component J k hJ hk = 0
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ J k hJ hk
    j.succ.succAboveOrderEmb.injective.injOn]
  have hmiss : j.succ ∉ J.image (SimplexCategory.δ j.succ).toOrderHom := by
    intro h
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
    exact Fin.succAbove_ne j.succ a ha
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedLiftData_other z
  · intro he
    exact hmiss (by rw [he]; simp)
  · intro he
    exact hmiss (by rw [he]; simp)

/-- 概要：正規化の最上位成分による評価は任意の負次数の元に届く。
方針：その元と微分だけを成分とする正規化された標準単体を取る。
規約：任意の dg 圏と二対象について追加仮定なく成立する。
使われ方：HA 1.3.1.12 の各項の同型の全射性。 -/
lemma normalizedTopEval_surjective (x y : D) (n : ℕ) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedTopEval (R := R) x y n) := by
  intro z
  exact ⟨⟨⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedLiftData z, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedLiftData_mem_standard z⟩, normalizedLift_mem z⟩,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedLiftData_top z⟩

/-- 概要：正次数の正規化された標準単体と対応する負次数の Hom は線形同値である。
方針：最上位評価の単射性と具体的な持ち上げによる全射性をまとめる。
規約：chain 次数 n+1 は cochain 次数 −(n+1) に対応する。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の正規化複体の各項の同定。 -/
def normalizedTopEquiv (x y : D) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizedSubmodule R x y (n + 1) ≃ₗ[R] GradedHom R x y (-(n + 1 : ℤ)) :=
  LinearEquiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedTopEval (R := R) x y n)
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedTopEval_injective x y n, normalizedTopEval_surjective x y n⟩

/-- 概要：Mathlib の標準 Hom の Moore 正規化の正次数の項は負次数 Hom と同型である。
方針：Moore 部分対象の具体化と最上位評価の線形同値を合成する。
規約：微分との両立と零次数の比較は複体の同型のために別途必要である。
使われ方：HA 1.3.1.12 の標準模型と切断 Hom の比較。 -/
def standardMoorePositiveIso (x y : D) (n : ℕ) :
    ((AlgebraicTopology.normalizedMooreComplex (ModuleCat.{u} R)).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).X (n + 1) ≅
        (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).X (-(n + 1 : ℤ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso (R := R) x y (n + 1) ≪≫
    (normalizedTopEquiv (R := R) x y n).toModuleIso

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
