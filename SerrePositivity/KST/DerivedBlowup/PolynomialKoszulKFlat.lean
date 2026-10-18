module

public import SerrePositivity.KST.DerivedBlowup.KoszulKFlat
public import Mathlib.RingTheory.Flat.Stability

/-!
概要：KST Lemma3.6 の多項式係数 Koszul 解消は普遍基底上でも K-flat。
方針：各項の多項式環上の自由性と係数環上の平坦性の推移性、および有限振幅を使う。
規約：試験複体は非有界。係数環への制限後の K-flat 性を実際に証明する。
使われ方：表示多項式環上の底変更を普遍基底上の導来底変更へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {I : Type v} {n : ℕ}

/-- 概要：多項式係数 Koszul 外積複体を基底係数へ制限した複体。
方針：多項式の定数係数構造射による各次数の係数制限を取る。
規約：KST Lemma3.6。使われ方：普遍基底上での K-flat 計算。 -/
abbrev polynomialKoszulRestriction (x : Fin n → MvPolynomial I R) :=
  ((ModuleCat.restrictScalars (algebraMap R (MvPolynomial I R))).mapHomologicalComplex
    (.up ℤ)).obj (sequenceExteriorCochain x)

/-- 概要：基底係数へ制限した多項式 Koszul 複体の各項は平坦。
方針：多項式環上の自由性と多項式環の係数環上の平坦性を推移させる。
規約：KST Lemma3.6。使われ方：非有界試験複体に対する K-flat 性。 -/
theorem polynomialKoszulRestriction_flat (x : Fin n → MvPolynomial I R) (q : ℤ) :
    Module.Flat R ((polynomialKoszulRestriction x).X q) := by
  let M := (sequenceExteriorCochain x).X q
  let : Module R M := Module.restrictScalars R (MvPolynomial I R) M
  let : IsScalarTower R (MvPolynomial I R) M :=
    IsScalarTower.restrictScalars R (MvPolynomial I R) M
  have : Module.Free (MvPolynomial I R) M := sequenceExteriorCochain_free x q
  have : Module.Flat (MvPolynomial I R) M := inferInstance
  exact Module.Flat.trans R (MvPolynomial I R) M

/-- 概要：基底係数へ制限した有限多項式 Koszul 複体は K-flat。
方針：係数制限後も振幅 [-n,0] が保たれ、各項が平坦であることを使う。
規約：KST Lemma3.6、比変数の型は Type で、係数環の宇宙は任意。
使われ方：普遍基底からの導来 tensor をこの具体的な解消で計算する。 -/
theorem polynomialKoszulRestriction_kFlat {J : Type} (x : Fin n → MvPolynomial J R) :
    DifferentialGraded.complexKFlat R (polynomialKoszulRestriction x) := by
  apply DifferentialGraded.complexKFlat_of_flat_bounds R _ (-(n : ℤ)) 0
  · intro q hq
    exact (ModuleCat.restrictScalars (algebraMap R (MvPolynomial J R))).map_isZero
      (sequenceExteriorCochain_isZero_X_lt x q hq)
  · intro q hq
    exact (ModuleCat.restrictScalars (algebraMap R (MvPolynomial J R))).map_isZero
      (exteriorKoszulCochain_isZero_X_pos _ q hq)
  · exact polynomialKoszulRestriction_flat x

/-- 概要：チャートの外積 Koszul 模型を元の基底環へ制限した複体。
方針：表示多項式環から基底への係数制限を取る。
規約：KST Def3.1。使われ方：普遍基底上の導来底変更の始域。 -/
abbrev chartRestrictedExterior {r : ℕ} (a : Fin (r + 1) → R) (i : Fin (r + 1)) :=
  ((ModuleCat.restrictScalars (algebraMap R (ChartRing R i))).mapHomologicalComplex
    (.up ℤ)).obj
      (chartExteriorCochain (fun j => MvPolynomial.C (a j)) (chartCoordinate R i) i)

/-- 概要：チャート外積模型は元の基底環上でも K-flat。
方針：有限列の外積模型との添字比較で、制限後の多項式 Koszul K-flat 性を移す。
規約：KST Lemma3.6。使われ方：任意係数への導来底変更の計算。 -/
theorem chartRestrictedExterior_kFlat {r : ℕ} (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    DifferentialGraded.complexKFlat R (chartRestrictedExterior a i) :=
  DifferentialGraded.complexKFlat_of_iso R
    (((ModuleCat.restrictScalars (algebraMap R (ChartRing R i))).mapHomologicalComplex
      (.up ℤ)).mapIso (chartSequenceExteriorIso a i)).symm
    (polynomialKoszulRestriction_kFlat (chartKoszulSequence a i))

end SerrePositivity.KST.DerivedBlowup
