module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedEquiv
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ConnectiveHom

/-!
# 標準 Hom の正規化の零次数

概要：標準 Hom の零単体は元の Hom の閉次数零の元と線形同値である。
方針：Fin 1 の非空部分集合は全体集合だけなので、その一成分で評価する。
規約：smart truncation の零次数は H⁰ の商ではなく閉元の部分加群である。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の正規化の零次数の比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：標準零単体を閉次数零の元へ評価する線形写像。
方針：唯一の非空集合で評価し、標準方程式の右辺が零であることを使う。
規約：閉元の部分加群へ値を取る。
使われ方：HA 1.3.1.12 の smart truncation の零次数。 -/
def standardZeroEval (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y 0 →ₗ[R] zeroCycles (homObject R D x y) where
  toFun f := ⟨f.val.component Finset.univ 0 Finset.univ_nonempty (by simp), by
    have h := f.property Finset.univ 0 Finset.univ_nonempty (by simp)
    change _root_.SerrePositivity.DifferentialGraded.differential R (f.val.component Finset.univ 0 _ _) = 0
    simpa [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs] using h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 概要：標準零単体の評価は単射である。
方針：全ての非空部分集合が Fin 1 全体に等しいことを使う。
規約：全体集合の評価だけで成分族を決める。
使われ方：HA 1.3.1.12 の零次数の同型の単射性。 -/
lemma standardZeroEval_injective (x y : D) :
    Function.Injective (standardZeroEval (R := R) x y) := by
  intro f g h
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  have hfull : J = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro a
    obtain ⟨b, hb⟩ := hJ
    have hab : b = a := by omega
    exact hab ▸ hb
  subst J
  have hkk : k = 0 := by simpa using hk
  subst hkk
  convert congrArg Subtype.val h using 1 <;> rfl

/-- 概要：閉次数零の元を標準零単体に持ち上げる。
方針：唯一の非空集合に指定値を置く一点支持の成分族を使う。
規約：閉性は標準方程式そのものである。
使われ方：HA 1.3.1.12 の零次数の同型の逆写像。 -/
def standardZeroLift (z : zeroCycles (homObject R D x y)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y 0 :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.singleComponent Finset.univ 0 Finset.univ_nonempty (by simp) z.val, by
    intro J k hJ hk
    have hfull : J = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro a
      obtain ⟨b, hb⟩ := hJ
      have hab : b = a := by omega
      exact hab ▸ hb
    subst J
    have hkk : k = 0 := by simpa using hk
    subst hkk
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.singleComponent_self]
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardRhs]⟩

/-- 概要：標準零単体の評価は全ての閉零元に届く。
方針：一点支持の持ち上げを評価する。
規約：商を取る前の閉元についての主張。
使われ方：HA 1.3.1.12 の零次数の同型の全射性。 -/
lemma standardZeroEval_surjective (x y : D) :
    Function.Surjective (standardZeroEval (R := R) x y) := by
  intro z
  refine ⟨standardZeroLift z, ?_⟩
  apply Subtype.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.singleComponent (n := 0) Finset.univ 0 Finset.univ_nonempty (by simp) z.val).component
    Finset.univ 0 Finset.univ_nonempty (by simp) = z.val
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.singleComponent_self (n := 0) _ _ _ _ z.val

/-- 概要：標準零単体と元の Hom の閉次数零の元は線形同値である。
方針：評価の単射性と一点支持による全射性をまとめる。
規約：零次数の符号は +1。
使われ方：HA 1.3.1.12 の正規化複体の零次数の同定。 -/
def standardZeroEquiv (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y 0 ≃ₗ[R] zeroCycles (homObject R D x y) :=
  LinearEquiv.ofBijective (standardZeroEval (R := R) x y)
    ⟨standardZeroEval_injective x y, standardZeroEval_surjective x y⟩

/-- 概要：標準 Hom の Moore 正規化の零次数は切断 Hom の零次数と同型である。
方針：零次数の正規化は全体なので、閉元の線形同値と切断の同型を合成する。
規約：微分との両立はまだ別途必要である。
使われ方：HA 1.3.1.12 の切断 Hom との比較。 -/
def standardMooreZeroIso (x y : D) :
    ((AlgebraicTopology.normalizedMooreComplex (ModuleCat.{u} R)).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).X 0 ≅ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex (R := R) x y).X 0 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso (R := R) x y 0 ≪≫
    (LinearEquiv.ofTop (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizedSubmodule R x y 0) rfl).toModuleIso ≪≫
    (standardZeroEquiv (R := R) x y).toModuleIso ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroCyclesIso (R := R) x y).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
