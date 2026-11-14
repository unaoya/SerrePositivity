module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.DerivedBlowup.LocalDGModels
public import SerrePositivity.KST.DerivedBlowup.ChartDGFunctors

/-!
概要：KST Lemma3.6 の E∩U_i と Ko(A;a)[S] の局所 dg 比較。
方針：関係式の列挙同型と自己逆 Koszul 基底変換を dg 関手として合成する。
規約：例外因子の dg 模型と多項式底変更を共通の全 a_j の外積模型へ送る。
使われ方：例外因子の射影空間表示と係数つき半直交分解。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R : Type u} [CommRing R] {r : ℕ}

/-- 概要：例外因子のチャート dg 圏から全 a_j の Koszul 外積 dg 圏への関手。
方針：Cartier 方程式を pivot に移し、例外因子の可逆基底変換を合成する。
規約：KST Lemma3.6。使われ方：E∩U_i の局所 dg 表示の比較。 -/
def exceptionalChartDGFunctor (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    EnrichedFunctor (DifferentialGraded.Complex (ChartRing R i))
      (ExceptionalChartObject a i)
      (ExteriorKoszulObject
        (Finsupp.linearCombination (ChartRing R i) (exceptionalProductSequence a i))) :=
  EnrichedFunctor.comp (DifferentialGraded.Complex (ChartRing R i))
    (exteriorKoszulDGFunctor (exceptionalSequenceGeneratorEquiv i).toLinearMap
      (Finsupp.linearCombination (ChartRing R i) (exceptionalChartSequence a i))
      (Finsupp.linearCombination (ChartRing R i)
        (exceptionalRelationValue (fun j => MvPolynomial.C (a j)) (chartCoordinate R i) i))
      (exceptionalSequenceGeneratorEquiv_differential a i))
    (exceptionalExteriorDGFunctor (fun j => MvPolynomial.C (a j)) (chartCoordinate R i) i)

/-- 概要：例外因子の局所 dg 比較は Hom 複体上で可逆。
方針：二つの生成元の線形同型の cochain 同型を合成する。
規約：KST Lemma3.6。使われ方：例外因子の局所準同値。 -/
theorem exceptionalChartDGFunctor_map_isIso (a : Fin (r + 1) → R) (i : Fin (r + 1)) (x y) :
    IsIso ((exceptionalChartDGFunctor a i).map x y) := by
  change IsIso
    ((exteriorKoszulCochainIso (exceptionalSequenceGeneratorEquiv i)
      (Finsupp.linearCombination (ChartRing R i) (exceptionalChartSequence a i))
      (Finsupp.linearCombination (ChartRing R i)
        (exceptionalRelationValue (fun j => MvPolynomial.C (a j)) (chartCoordinate R i) i))
      (exceptionalSequenceGeneratorEquiv_differential a i)).hom ≫
        (exceptionalExteriorCochainIso (fun j => MvPolynomial.C (a j)) (chartCoordinate R i) i).hom)
  infer_instance

/-- 概要：例外因子の局所 dg 比較は準同値。
方針：Hom 同型と一対象の H⁰ 上の全射性を使う。
規約：KST Lemma3.6。使われ方：例外因子の局所 perfect 加群圏の比較。 -/
theorem exceptionalChartDGFunctor_quasiEquivalence (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    DifferentialGraded.QuasiEquivalence (exceptionalChartDGFunctor a i) := by
  constructor
  · intro x y
    have := exceptionalChartDGFunctor_map_isIso a i x y
    infer_instance
  · apply Functor.essSurj_of_surj
    rintro ⟨y⟩
    change ExteriorKoszulObject
      (Finsupp.linearCombination (ChartRing R i) (exceptionalProductSequence a i)) at y
    cases y
    exact ⟨⟨ExteriorKoszulObject.point⟩, rfl⟩

/-- 概要：Ko(A;a) の多項式底変更を例外因子と共通の dg 模型へ送る。
方針：一般の自由 Koszul dg 底変更を多項式係数射に適用する。
規約：KST Lemma3.6。使われ方：Ko(A;a)[S] の dg 比較のもう一方の射。 -/
def exceptionalPolynomialBaseChangeDGFunctor (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    EnrichedFunctor (DifferentialGraded.Complex (ChartRing R i))
      (DifferentialGraded.ScalarExtension.DGBaseChange
        (MvPolynomial.C : R →+* ChartRing R i)
        (ExteriorKoszulObject (Finsupp.linearCombination R a)))
      (ExteriorKoszulObject
        (Finsupp.linearCombination (ChartRing R i) (exceptionalProductSequence a i))) :=
  freeKoszulBaseChangeDGFunctor MvPolynomial.C a

/-- 概要：Ko(A;a) の多項式底変更から共通 dg 模型への関手は準同値。
方針：一般の自由 Koszul 底変更の準同値性を使う。
規約：KST Lemma3.6。使われ方：E∩U_i と Ko(A;a)[S] の dg 比較。 -/
theorem exceptionalPolynomialBaseChangeDGFunctor_quasiEquivalence
    (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    DifferentialGraded.QuasiEquivalence (exceptionalPolynomialBaseChangeDGFunctor a i) :=
  freeKoszulBaseChangeDGFunctor_quasiEquivalence MvPolynomial.C a

end SerrePositivity.KST.DerivedBlowup

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Construction §3.1 thickenings" (partial := component) "仮定：明示的な例外因子のチャート dg 模型と有限重なり（Lean が強い）。結論：例外因子のチャート比較と完全加群の比較。D(n) と E(n) を含む導来スキーム全体の厚化・立方体は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.exceptionalPolynomialBaseChangeDGFunctor_quasiEquivalence
attribute [cite KST "Eq (3.3)" (partial := component) "仮定：明示的な例外因子のチャート dg 模型と有限重なり（Lean が強い）。結論：例外因子のチャート比較と完全加群の比較。D(n) と E(n) を含む導来スキーム全体の厚化・立方体は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.exceptionalPolynomialBaseChangeDGFunctor_quasiEquivalence
attribute [cite KST "Lemma 3.6" (partial := component) "仮定：普遍多項式模型からの指定された底変換（Lean が強い）。結論：係数環・例外因子上の明示的比較は得るが、任意の二つの正則列表示に対する正方形と全厚化の独立性は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.exceptionalPolynomialBaseChangeDGFunctor_quasiEquivalence
attribute [cite KST "Rem 3.2" (partial := component) "仮定：明示的な例外因子のチャート dg 模型と有限重なり（Lean が強い）。結論：例外因子のチャート比較と完全加群の比較。D(n) と E(n) を含む導来スキーム全体の厚化・立方体は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.DerivedBlowup.exceptionalPolynomialBaseChangeDGFunctor_quasiEquivalence
