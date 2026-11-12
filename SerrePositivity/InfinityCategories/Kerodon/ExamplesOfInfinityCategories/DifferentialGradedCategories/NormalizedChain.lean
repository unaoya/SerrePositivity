module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedDifferential

/-!
# 標準 Hom の正規化と切断 Hom の複体の比較

概要：正規化の各項の同型を微分と可換な複体の同型へまとめる。
方針：正次数間では最上位成分、次数1から0では閉元の包含で等式を検査する。
規約：零次数は smart truncation の閉元であり、追加の符号を使わない。
使われ方：HA 1.3.1.12–1.3.1.13、Kerodon 2.5.6（Tag 00QQ） の実際の Mathlib Γ との同定。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open DifferentialGraded
open scoped _root_.Simplicial

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

/-- 概要：切断の零項と具体的閉元の同型は元の零項への包含と可換である。
方針：抽象的 cycles と具体的な核の同型の包含への可換性を合成する。
規約：元の Hom の零項へ戻して比較する。
使われ方：HA 1.3.1.12 の零次数への微分の検査。 -/
lemma connectiveHomComplex_zeroCyclesIso_hom_subtype (x y : D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroCyclesIso (R := R) x y).hom ≫
      ModuleCat.ofHom (_root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject R D x y)).subtype =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroIso (R := R) x y).hom ≫ (homObject R D x y).iCycles 0 := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroCyclesIso, Iso.trans_hom]
  rw [Category.assoc, Category.assoc]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroIso (R := R) x y).hom ≫
    ((_root_.SerrePositivity.DifferentialGraded.homObject R D x y).cyclesIsoSc' (-1) 0 1 (by simp) (by simp)).hom ≫
      (((_root_.SerrePositivity.DifferentialGraded.homObject R D x y).sc' (-1) 0 1).moduleCatCyclesIso.hom ≫
        ((_root_.SerrePositivity.DifferentialGraded.homObject R D x y).sc' (-1) 0 1).moduleCatLeftHomologyData.i) = _
  rw [ShortComplex.moduleCatCyclesIso_hom_i,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles]

/-- 概要：次数1から0への Moore 微分は閉元への微分に一致する。
方針：閉元の包含で検査し、零番目の面の最上位成分を使う。
規約：終対象はホモロジーではなく cycles である。
使われ方：HA 1.3.1.12 の正規化と切断 Hom の複体の同型の零次数部分。 -/
lemma standardMooreZeroIso_d (x y : D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMoorePositiveIso (R := R) x y 0).hom ≫ (homObject R D x y).toCycles (-1) 0 =
      ((normalizedMooreComplex (ModuleCat.{u} R)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).d 1 0 ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreZeroIso (R := R) x y).hom ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_zeroIso (R := R) x y).hom := by
  apply (cancel_mono ((_root_.SerrePositivity.DifferentialGraded.homObject R D x y).iCycles 0)).mp
  rw [Category.assoc, HomologicalComplex.toCycles_i]
  simp only [Category.assoc]
  rw [← connectiveHomComplex_zeroCyclesIso_hom_subtype]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreZeroIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  apply ConcreteCategory.hom_ext
  intro s
  change (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).d (-1) 0
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso (R := R) x y 1).hom s).val.val.component
      Finset.univ (-1) Finset.univ_nonempty (by simp)) =
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso (R := R) x y 0).hom
      (((normalizedMooreComplex (ModuleCat.{u} R)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).d
        1 0 s)).val.val.component Finset.univ 0 Finset.univ_nonempty (by simp))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso_d_val, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFaceZero_top]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalized_top_d _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso (R := R) x y 1).hom s).property
    (-1) 0 (by simp) (by omega)

/-- 概要：標準 Hom の正規化の全ての項を切断 Hom の項に同定する。
方針：零次数と正次数の同型を次数によってまとめる。
規約：正次数の微分は同じ δ を用いる。
使われ方：HA 1.3.1.12 の複体の同型の各項。 -/
def standardNormalizationTermIso (x y : D) : ∀ n : ℕ,
    ((normalizedMooreComplex (ModuleCat.{u} R)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).X n ≅
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex (R := R) x y).X n
  | 0 => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreZeroIso (R := R) x y
  | n + 1 => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMoorePositiveIso (R := R) x y n ≪≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_positiveIso (R := R) x y n).symm

/-- 概要：正規化と切断 Hom の各項の同型は微分と可換である。
方針：終次数が零か正かで場合分けし、既に計算した微分の式を適用する。
規約：chain 微分の始次数は終次数 +1。
使われ方：HA 1.3.1.12 の複体の同型の可換条件。 -/
lemma standardNormalizationTermIso_d (x y : D) (n : ℕ) :
    (standardNormalizationTermIso (R := R) x y (n + 1)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex (R := R) x y).d (n + 1) n =
        ((normalizedMooreComplex (ModuleCat.{u} R)).obj
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).d (n + 1) n ≫
            (standardNormalizationTermIso (R := R) x y n).hom := by
  cases n with
  | zero =>
    dsimp only [standardNormalizationTermIso, Iso.trans_hom, Iso.symm_hom]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_d_zero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, standardMooreZeroIso_d]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  | succ n =>
    dsimp only [standardNormalizationTermIso, Iso.trans_hom, Iso.symm_hom]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex_d_positive]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMoorePositiveIso_d (R := R) x y n
    rw [← Category.assoc, h]
    simp only [Category.assoc]

/-- 概要：標準 Hom の実際の Moore 正規化は切断 Hom と複体として同型である。
方針：全ての各項の同型と微分との可換性から複体の同型を作る。
規約：標準模型側の正規化を仮定せず計算した結果である。
使われ方：HA 1.3.1.12–1.3.1.13 の Mathlib Γ との同定。 -/
def standardNormalizationIso (x y : D) :
    (normalizedMooreComplex (ModuleCat.{u} R)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.connectiveHomComplex (R := R) x y :=
  HomologicalComplex.Hom.isoOfComponents (standardNormalizationTermIso (R := R) x y)
    (by
      intro i j hij
      have hi : i = j + 1 := by simpa using hij.symm
      subst hi
      exact standardNormalizationTermIso_d x y j)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
