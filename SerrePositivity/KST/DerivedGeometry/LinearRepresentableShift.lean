module

public import SerrePositivity.KST.DerivedGeometry.LinearComplexShift
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Module.Graded

/-!
# 複体 dg 圏の代表加群の shift の具体的表示

概要：代表右 dg 加群の shift が、元の複体の shift により表現されることを示す。
方針：写像複体の右 shift 同型を全次数の作用と比較する。
規約：次数零の自然性だけで済ませず、shift 作用の符号も照合する。
使われ方：Drinfeld §2.4、KST D4・§10-7、Toën §3.2 の前三角化比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.KST.DerivedGeometry.LinearComplex

variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]

attribute [local instance] enrichment

/--
概要：複体 dg 圏の豊穣順合成を、符号付きの cochain 合成で計算する。
方針：実際の写像複体のテンソル成分公式を使う。
規約：第一射の次数と第二射の次数の積の Koszul 符号を維持する。
使われ方：Drinfeld §2.4、KST D4 の代表加群の全次数の自然性。
-/
lemma forward_cochain {X Y Z : CochainComplex C ℤ} {p q n : ℤ}
    (f : Cochain X Y p) (g : Cochain Y Z q) (h : p + q = n) :
    forward A (D := CochainComplex C ℤ) (x := X) (y := Y) (z := Z) f g h =
      (p * q).negOnePow • f.comp g h :=
  forwardComposition_apply X Y Z p q n h f g

/--
概要：写像複体の右 shift 比較は、代表加群の全次数の作用と両立する。
方針：shift 作用の符号、豊穣合成の符号、右 shift と前合成の可換性を照合する。
規約：対象圏は任意の線形加法圏。
使われ方：Drinfeld §2.4、KST D4 の代表加群の shift の表示。
-/
theorem representableShift_naturality (Y : CochainComplex C ℤ) (s : ℤ)
    (x y : (CochainComplex C ℤ)ᵒᵖ) :
    (shiftModule s (representable A Y)).map x y ≫
        homPostcompose _ (mappingShiftMap A y.unop Y s) =
      (representable A (Y⟦s⟧)).map x y ≫ homPrecompose (mappingShiftMap A x.unop Y s) _ := by
  apply closedFamily_of_action A
    (M := shiftModule s (representable A Y)) (N := representable A (Y⟦s⟧))
    (fun z => mappingShiftMap A z.unop Y s) ?_ x y
  intro x y p r n hn f g
  unfold moduleAction
  rw [shiftModule_map_v]
  change (mappingShiftMap A y.unop Y s).f n
      ((s * p).negOnePow •
        (((representableMap A Y x y).f p f).v (r + s) (n + s) (by omega) g)) =
    (((representableMap A (Y⟦s⟧) x y).f p f).v r n hn
      ((mappingShiftMap A x.unop Y s).f r g))
  rw [representableMap_apply, representableMap_apply]
  rw [forward_cochain, forward_cochain]
  change ((s * p).negOnePow • ((p * (r + s)).negOnePow • f.comp g _)).rightShift s n rfl =
    (p * r).negOnePow • f.comp (g.rightShift s r rfl) _
  rw [Cochain.rightShift_units_smul, Cochain.rightShift_units_smul,
    rightShift_comp f g (by omega) rfl rfl, smul_smul]
  have hsign : (s * p).negOnePow * (p * (r + s)).negOnePow = (p * r).negOnePow := by
    rw [mul_add, Int.negOnePow_add, mul_comm s p]
    calc
      (p * s).negOnePow * ((p * r).negOnePow * (p * s).negOnePow) =
          (p * r).negOnePow * ((p * s).negOnePow * (p * s).negOnePow) := by ac_rfl
      _ = (p * r).negOnePow := by rw [Int.units_mul_self, mul_one]
  rw [hsign]

variable [Small.{u} (CochainComplex C ℤ)]

/--
概要：代表右加群の shift から、shift した複体の代表右加群への射。
方針：具体的な写像複体の右 shift 比較と全次数自然性を束ねる。
規約：元の複体の有界性や平坦性を要求しない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の前三角化の代表可能性。
-/
def representableShiftMap (Y : CochainComplex C ℤ) (s : ℤ) :
    ForgetEnrichment.of (Complex A) (shiftModule s (representable A Y)) ⟶
      ForgetEnrichment.of (Complex A) (representable A (Y⟦s⟧)) :=
  moduleMorphismMk A (CochainComplex C ℤ) (fun x => mappingShiftMap A x.unop Y s)
    (representableShift_naturality A Y s)

/--
概要：代表右加群の shift は、shift した複体の代表右加群と同型。
方針：全次数自然な写像複体の右 shift 同型を加群同型へ束ねる。
規約：成分の逆写像も全次数自然であることを既存の証明で保証する。
使われ方：Drinfeld §2.4、KST D4・§10-7 の前三角化の代表可能性。
-/
def representableShiftIso (Y : CochainComplex C ℤ) (s : ℤ) :
    ForgetEnrichment.of (Complex A) (shiftModule s (representable A Y)) ≅
      ForgetEnrichment.of (Complex A) (representable A (Y⟦s⟧)) :=
  moduleIsoMk A (CochainComplex C ℤ) (fun x => mappingShiftIso A x.unop Y s)
    (representableShift_naturality A Y s)

/--
概要：構成した代表加群の右 shift 比較射は同型。
方針：実際の加群同型の順射との定義上の一致を使う。
規約：対象ごとの同型性だけでなく全次数自然性も証明済み。
使われ方：Drinfeld §2.4、KST D4 の有限 cell の shift 閉性。
-/
instance representableShiftMap_isIso (Y : CochainComplex C ℤ) (s : ℤ) :
    IsIso (representableShiftMap A Y s) := by
  change IsIso (representableShiftIso A Y s).hom
  infer_instance

/--
概要：代表加群の shift 同型を評価すると具体的な写像複体の同型に戻る。
方針：加群同型の評価公式を使う。
規約：同じ chain map と同じ符号を維持する。
使われ方：Drinfeld §2.4、KST D4 の比較正方形。
-/
lemma representableShiftIso_hom_eval (Y T : CochainComplex C ℤ) (s : ℤ) :
    (moduleEvaluation A (CochainComplex C ℤ) T).map (representableShiftIso A Y s).hom =
      mappingShiftMap A T Y s := moduleIsoMk_hom_eval A (CochainComplex C ℤ) _ _ T

end SerrePositivity.KST.DerivedGeometry.LinearComplex
