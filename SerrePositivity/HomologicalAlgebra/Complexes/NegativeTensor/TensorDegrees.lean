module

public import SerrePositivity.HomologicalAlgebra.Complexes.NegativeTensor.Degrees

/-!
# 零延長とテンソルの次数ごとの比較

概要：Berger–Fresse §1.1 の鎖次数の変更を二因子テンソルと接続する。
方針：直和からの射を各因子の標準同型で定め、正次数の因子を消す。
規約：自然数全次数 n は整数全次数 −n に対応する。
使われ方：AW 鎖写像の整数コチェイン模型への移送。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.NegativeTensor

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable {A : Type u} [CommRing A]

/-- 概要：テンソルの自然数全次数を延長後の負次数へ移す（Berger–Fresse §1.1）。
方針：各二次数で標準同型の逆をテンソルし、全テンソルへ含める。
規約：入力は自然数テンソル、出力は既存の整数テンソル。
使われ方：延長とテンソルの標準比較の順方向。 -/
def degreeMap (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj K L).X n ⟶
      (HomologicalComplex.tensorObj (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L)).X (-(n : ℤ)) :=
  mapBifunctorDesc (fun p q hpq =>
    ((_root_.SerrePositivity.NegativeTensor.xIso K p).inv ⊗ₘ (_root_.SerrePositivity.NegativeTensor.xIso L q).inv) ≫
      ιTensorObj (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (by
        change p + q = n at hpq
        omega))

/-- 概要：順方向の次数比較の斉次成分（Berger–Fresse §1.1）。
方針：直和からの射の普遍性を使う。
規約：全次数の任意の等式を許す。
使われ方：比較写像の逆性と微分との可換性。 -/
@[reassoc (attr := simp)]
lemma ι_degreeMap (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n p q : ℕ)
    (h : p + q = n) :
    ιTensorObj K L p q n h ≫ _root_.SerrePositivity.NegativeTensor.degreeMap K L n =
      ((_root_.SerrePositivity.NegativeTensor.xIso K p).inv ⊗ₘ (_root_.SerrePositivity.NegativeTensor.xIso L q).inv) ≫
        ιTensorObj (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (by omega) :=
  ι_mapBifunctorDesc _ _ _ _

/-- 概要：非正整数次数を対応する自然数鎖次数と同定する（Berger–Fresse §1.1）。
方針：次数埋め込みの像の等式で標準同型を取る。
規約：鎖次数は (−i).toNat。
使われ方：整数テンソルの逆方向の次数比較。 -/
def xIsoNonpos (K : ChainComplex (ModuleCat.{u} A) ℕ) (i : ℤ) (hi : i ≤ 0) :
    (_root_.SerrePositivity.NegativeTensor.extend K).X i ≅ K.X (-i).toNat :=
  K.extendXIso ComplexShape.embeddingDownNat (by
    change -(((-i).toNat : ℕ) : ℤ) = i
    omega)

/-- 概要：逆方向の次数比較の全整数次数の成分（Berger–Fresse §1.1）。
方針：非正次数では標準同型をテンソルし、正次数では零を取る。
規約：全次数は −n。
使われ方：直和からの次数比較を構成する。 -/
def inverseComponent (K L : ChainComplex (ModuleCat.{u} A) ℕ)
    (n : ℕ) (r s : ℤ) (h : r + s = -(n : ℤ)) :
    (_root_.SerrePositivity.NegativeTensor.extend K).X r ⊗ (_root_.SerrePositivity.NegativeTensor.extend L).X s ⟶ (HomologicalComplex.tensorObj K L).X n :=
  if hr : r ≤ 0 then
    if hs : s ≤ 0 then
      ((_root_.SerrePositivity.NegativeTensor.xIsoNonpos K r hr).hom ⊗ₘ (_root_.SerrePositivity.NegativeTensor.xIsoNonpos L s hs).hom) ≫
        ιTensorObj K L (-r).toNat (-s).toNat n (by omega)
    else 0
  else 0

private lemma inverseComponent_neg (K L : ChainComplex (ModuleCat.{u} A) ℕ)
    (n p q : ℕ) (h : p + q = n) :
    _root_.SerrePositivity.NegativeTensor.inverseComponent K L n (-(p : ℤ)) (-(q : ℤ)) (by omega) =
      ((_root_.SerrePositivity.NegativeTensor.xIso K p).hom ⊗ₘ (_root_.SerrePositivity.NegativeTensor.xIso L q).hom) ≫ ιTensorObj K L p q n h := by
  rw [_root_.SerrePositivity.NegativeTensor.inverseComponent, dite_eq_left (show -(p : ℤ) ≤ 0 by omega),
    dite_eq_left (show -(q : ℤ) ≤ 0 by omega)]
  cases p <;> cases q <;> rfl

/-- 概要：延長後のテンソルの負次数を元の自然数全次数へ戻す（Berger–Fresse §1.1）。
方針：非正次数の直和因子を標準同型で戻し、正次数の因子は零とする。
規約：整数の全ての次数分割を扱う。
使われ方：延長とテンソルの標準比較の逆方向。 -/
def degreeInv (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L)).X (-(n : ℤ)) ⟶
      (HomologicalComplex.tensorObj K L).X n :=
  mapBifunctorDesc (fun r s h => _root_.SerrePositivity.NegativeTensor.inverseComponent K L n r s h)

/-- 概要：逆方向の次数比較の負次数成分（Berger–Fresse §1.1）。
方針：直和の普遍性と非正次数での成分の公式を使う。
規約：二次数は −p,−q、全次数は −n。
使われ方：二つの次数比較の逆性を検証する。 -/
@[reassoc (attr := simp)]
lemma ι_degreeInv (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n p q : ℕ)
    (h : p + q = n) :
    ιTensorObj (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (by omega) ≫
        _root_.SerrePositivity.NegativeTensor.degreeInv K L n =
      ((_root_.SerrePositivity.NegativeTensor.xIso K p).hom ⊗ₘ (_root_.SerrePositivity.NegativeTensor.xIso L q).hom) ≫ ιTensorObj K L p q n h := by
  rw [_root_.SerrePositivity.NegativeTensor.degreeInv, ι_mapBifunctorDesc]
  exact _root_.SerrePositivity.NegativeTensor.inverseComponent_neg K L n p q h

/-- 概要：自然数次数から移して戻すと恒等射（Berger–Fresse §1.1 の次数比較）。
方針：各直和成分で同型と逆同型のテンソルを消す。
規約：係数環の有限性・標数を仮定しない。
使われ方：テンソルの次数比較を同型として構成する。 -/
lemma degreeMap_inv (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    _root_.SerrePositivity.NegativeTensor.degreeMap K L n ≫ _root_.SerrePositivity.NegativeTensor.degreeInv K L n = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro p q h
  change p + q = n at h
  rw [_root_.SerrePositivity.NegativeTensor.ι_degreeMap_assoc, _root_.SerrePositivity.NegativeTensor.ι_degreeInv K L n p q h]
  simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, Iso.inv_hom_id,
    tensorHom_id, MonoidalCategory.id_whiskerRight, Category.id_comp, Category.comp_id]

/-- 概要：負次数から戻して移すと恒等射（Berger–Fresse §1.1 の次数比較）。
方針：正次数の因子は零、残る二次数は自然数の負号として比較する。
規約：整数テンソルの全直和因子で等式を検査する。
使われ方：テンソルの次数比較を同型として構成する。 -/
lemma degreeInv_map (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    _root_.SerrePositivity.NegativeTensor.degreeInv K L n ≫ _root_.SerrePositivity.NegativeTensor.degreeMap K L n = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro r s hrs
  change r + s = -(n : ℤ) at hrs
  by_cases hr : 0 < r
  · exact (Functor.map_isZero (tensorRight ((_root_.SerrePositivity.NegativeTensor.extend L).X s))
      (_root_.SerrePositivity.NegativeTensor.isZero_positive K r hr)).eq_of_src _ _
  by_cases hs : 0 < s
  · exact (Functor.map_isZero (tensorLeft ((_root_.SerrePositivity.NegativeTensor.extend K).X r))
      (_root_.SerrePositivity.NegativeTensor.isZero_positive L s hs)).eq_of_src _ _
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, r = -(p : ℤ) := ⟨(-r).toNat, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, s = -(q : ℤ) := ⟨(-s).toNat, by omega⟩
  have hpq : p + q = n := by omega
  rw [_root_.SerrePositivity.NegativeTensor.ι_degreeInv_assoc K L n p q hpq, _root_.SerrePositivity.NegativeTensor.ι_degreeMap]
  simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id,
    tensorHom_id, MonoidalCategory.id_whiskerRight, Category.id_comp, Category.comp_id]

/-- 概要：零延長とテンソルの負次数での標準同型（Berger–Fresse §1.1）。
方針：互いに逆な直和比較写像を束ねる。
規約：自然数次数 n と整数次数 −n を対応させる。
使われ方：AW 対角の整数複体への移送の次数ごとの同型。 -/
def degreeIso (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj K L).X n ≅
      (HomologicalComplex.tensorObj (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L)).X (-(n : ℤ)) where
  hom := _root_.SerrePositivity.NegativeTensor.degreeMap K L n
  inv := _root_.SerrePositivity.NegativeTensor.degreeInv K L n
  hom_inv_id := _root_.SerrePositivity.NegativeTensor.degreeMap_inv K L n
  inv_hom_id := _root_.SerrePositivity.NegativeTensor.degreeInv_map K L n

end SerrePositivity.NegativeTensor
