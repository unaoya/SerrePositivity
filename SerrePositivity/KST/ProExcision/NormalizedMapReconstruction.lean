module
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence

/-!
# 正規化鎖写像から実単体的射への復元

概要：Dold–Kan の実同値の充満忠実性を使い、正規化鎖写像を単体的射へ戻す。
方針：Mathlib の同値の前像を使い、合成・等式を正規化後の写像で検出する。
規約：KST Construction A.5 の区間復元。復元の存在を追加仮定にはしない。
使われ方：実テンソル区間から構成した鎖写像の単体的な区間射への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
open CategoryTheory AlgebraicTopology
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {X Y Z : SimplicialObject A}

/-- 概要：正規化した鎖写像を実単体的射へ復元する。
方針：Dold–Kan 同値の充満な関手の前像を使う。
規約：KST A.5、任意のアーベル圏。
使われ方：区間の実鎖写像から単体的区間写像を得る。 -/
def normalizedMapReconstruct
    (f : (normalizedMooreComplex A).obj X ⟶ (normalizedMooreComplex A).obj Y) : X ⟶ Y :=
  (CategoryTheory.Abelian.DoldKan.equivalence (A := A)).functor.preimage f

/-- 概要：復元した射の正規化は元の鎖写像に一致。
方針：充満な関手の前像の評価公式を使う。
規約：KST A.5。使われ方：区間の両端と自然性の検証。 -/
@[simp] lemma normalizedMapReconstruct_map
    (f : (normalizedMooreComplex A).obj X ⟶ (normalizedMooreComplex A).obj Y) :
    (normalizedMooreComplex A).map (normalizedMapReconstruct f) = f :=
  (CategoryTheory.Abelian.DoldKan.equivalence (A := A)).functor.map_preimage f

/-- 概要：二つの単体的射の等式は正規化した鎖写像の等式で検出できる。
方針：Dold–Kan 同値の忠実性を使う。
規約：KST A.5。使われ方：区間の両端と同変性を鎖計算へ帰着する。 -/
lemma normalizedMap_eq_of_map_eq (f g : X ⟶ Y)
    (h : (normalizedMooreComplex A).map f = (normalizedMooreComplex A).map g) : f = g :=
  (CategoryTheory.Abelian.DoldKan.equivalence (A := A)).functor.map_injective h

/-- 概要：単体的射の正規化を復元すると元の射を得る。
方針：正規化後の一致と忠実性を使う。
規約：KST A.5。使われ方：両端に指定した実射の復元。 -/
@[simp] lemma normalizedMapReconstruct_of_map (f : X ⟶ Y) :
    normalizedMapReconstruct ((normalizedMooreComplex A).map f) = f := by
  apply normalizedMap_eq_of_map_eq
  exact normalizedMapReconstruct_map _

/-- 概要：鎖写像の合成の復元は単体的射の合成。
方針：正規化の合成則と復元の評価公式で検出する。
規約：KST A.5。使われ方：入力射と外部群の作用への自然性の復元。 -/
lemma normalizedMapReconstruct_comp
    (f : (normalizedMooreComplex A).obj X ⟶ (normalizedMooreComplex A).obj Y)
    (g : (normalizedMooreComplex A).obj Y ⟶ (normalizedMooreComplex A).obj Z) :
    normalizedMapReconstruct (f ≫ g) = normalizedMapReconstruct f ≫ normalizedMapReconstruct g := by
  apply normalizedMap_eq_of_map_eq
  rw [CategoryTheory.Functor.map_comp, normalizedMapReconstruct_map,
    normalizedMapReconstruct_map, normalizedMapReconstruct_map]

end SerrePositivity.KST.ProExcision
