module
public import SerrePositivity.KST.SConstruction.InnerZeroDirectionComparison
public import SerrePositivity.KST.SConstruction.DiagonalIterationComponents

/-! # 内側の可変次数の比較と全単体的な比較の一致
概要：零方向の包含との可換性を持つ比較を、既存の全単体的な座標同型と照合する。
方針：等号の輸送を外側の S で写す式を使い、次数ごとの成分を反復数について比較する。
規約：既存の公開名と型を維持する。使われ方：全零境界への降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open scoped Simplicial

/-- 概要：対角添字への等号による輸送は外側の S への後合成と可換。
方針：等号の射を関手で写す公式を使い、各成分で証明する。
規約：自己関手の自然変換の厳密等号。使われ方：比較の成分の帰納。 -/
lemma innerDiagonalTransport_succ (r n : ℕ) :
    (multiSEndofunctor.{u} (r + 2)).map
      (eqToHom (innerVariableIndex_obj_diagonal (r + 1) (Opposite.op ⦋n⦌))) =
      Functor.whiskerRight
        ((multiSEndofunctor (r + 1)).map
          (eqToHom (innerVariableIndex_obj_diagonal r (Opposite.op ⦋n⦌))))
        (sEndofunctor n) := by
  simp only [eqToHom_map]
  apply NatTrans.ext
  funext X
  change (eqToHom (congrArg (multiSEndofunctor (r + 2)).obj
      (innerVariableIndex_obj_diagonal (r + 1) (Opposite.op ⦋n⦌)))).app X =
    (sEndofunctor n).map ((eqToHom (congrArg (multiSEndofunctor (r + 1)).obj
      (innerVariableIndex_obj_diagonal r (Opposite.op ⦋n⦌)))).app X)
  simp only [eqToHom_app, eqToHom_map]

/-- 概要：内側の比較の反復零回の成分は恒等射。
方針：右単位子と恒等な添字の輸送を計算する。
規約：任意の安定な入力。使われ方：成分比較の始点。 -/
lemma innerDiagonalComparisonIso_zero_app (n : ℕ) (X : StableModel.{u}) :
    (innerDiagonalComparisonIso 0 n).hom.app X = 𝟙 ((sEndofunctor n).obj X) := by
  simp [innerDiagonalComparisonIso, innerVariableSComparisonIso, innerVariableIndex,
    Nat.recAux, multiSEndofunctor]

/-- 概要：内側の比較の成分は外側の S で写す再帰式を満たす。
方針：結合子の成分と対角添字の輸送を外側の S にまとめる。
規約：厳密な成分の等号。使われ方：次数別の固定比較との一致。 -/
lemma innerDiagonalComparisonIso_succ_app (r n : ℕ) (X : StableModel.{u}) :
    (innerDiagonalComparisonIso (r + 1) n).hom.app X =
      (sEndofunctor n).map ((innerDiagonalComparisonIso r n).hom.app X) := by
  simp only [innerDiagonalComparisonIso, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
  rw [innerDiagonalTransport_succ]
  change (𝟙 _ ≫ (sEndofunctor n).map
      ((innerVariableSComparisonIso r (fun _ => Opposite.op ⦋n⦌) (Opposite.op ⦋n⦌)).hom.app X)) ≫
      (sEndofunctor n).map
        (((multiSEndofunctor (r + 1)).map
          (eqToHom (innerVariableIndex_obj_diagonal r (Opposite.op ⦋n⦌)))).app X) = _
  rw [Category.id_comp, ← CategoryTheory.Functor.map_comp]
  rfl

/-- 概要：内側の対角比較は固定次数の結合子による比較に一致。
方針：反復数について成分の再帰式を比較する。
規約：自然変換そのものの等号。使われ方：全単体的比較との照合。 -/
lemma innerDiagonalComparisonIso_hom_eq (r n : ℕ) :
    (innerDiagonalComparisonIso.{u} r n).hom =
      (multiSEndofunctor_diagonal_inner_iso r n).hom := by
  induction r with
  | zero =>
    apply NatTrans.ext
    funext X
    exact innerDiagonalComparisonIso_zero_app n X
  | succ r ih =>
    apply NatTrans.ext
    funext X
    calc
      _ = (sEndofunctor n).map ((innerDiagonalComparisonIso r n).hom.app X) :=
        innerDiagonalComparisonIso_succ_app r n X
      _ = (sEndofunctor n).map
          ((multiSEndofunctor_diagonal_inner_iso r n).hom.app X) :=
        congrArg (sEndofunctor n).map (NatTrans.congr_app ih X)
      _ = _ := by
        change _ = 𝟙 _ ≫ (sEndofunctor n).map
          ((multiSEndofunctor_diagonal_inner_iso r n).hom.app X)
        exact (Category.id_comp _).symm

/-- 概要：既存の全単体的な比較と零方向の包含に使う比較は各次数で一致。
方針：固定次数の結合子による比較を介する。
規約：公開されている二つの同型の射の厳密等号。使われ方：全零境界への降下。 -/
lemma diagonalSInnerComparisonNatIso_app_eq_inner (r n : ℕ) :
    (diagonalSInnerComparisonNatIso.{u} r).hom.app (Opposite.op ⦋n⦌) =
      (innerDiagonalComparisonIso r n).hom :=
  (diagonalSInnerComparisonNatIso_app_eq r n).trans (innerDiagonalComparisonIso_hom_eq r n).symm

end SerrePositivity.KST.SConstruction
