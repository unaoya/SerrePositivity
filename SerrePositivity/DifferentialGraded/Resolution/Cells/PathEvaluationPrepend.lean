module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathEvaluation
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathComposition
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinEvaluation

/-! # 元のHomを先頭合成する操作と有限path評価の整合性

## 概要
元のHomを先頭合成する操作と有限path評価の整合性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w}
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

lemma pathEvaluation_prepend (w : List I) (x y z : D) :
    (Cochain.ofHom (C.prependMap A D I w x y z)).comp (P.pathEvaluation w x z) (zero_add 0) =
    (tensorZeroCochain (Cochain.ofHom (F.map x y)) (P.pathEvaluation w y z)).comp
      (Cochain.ofHom (eComp (Complex A) (F.obj x)
        (F.obj y) (F.obj z))) (zero_add 0) := by
  cases w with
  | nil =>
    simpa only [pathEvaluation_nil, Family.prependMap, tensorZeroCochain_ofHom,
      ← Cochain.ofHom_comp] using
      congrArg (fun f => Cochain.ofHom f) (F.map_comp x y z)
  | cons b w =>
    have h := tensorJoin_evaluation
      (homObject A D x y) (homObject A D y (C.source b)) (homObject A D x (C.source b))
      (homObject A E (F.obj x) (F.obj y))
      (homObject A E (F.obj y) (F.obj (C.source b)))
      (homObject A E (F.obj x) (F.obj (C.source b)))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) z)
      (homObject A E (F.obj (C.source b)) (F.obj z))
      (homObject A E (F.obj y) (F.obj z))
      (homObject A E (F.obj x) (F.obj z))
      (F.map x y) (F.map y (C.source b)) (F.map x (C.source b))
      (eComp (Complex A) x y (C.source b))
      (eComp (Complex A) (F.obj x) (F.obj y) (F.obj (C.source b)))
      (eComp (Complex A) (F.obj x) (F.obj (C.source b)) (F.obj z))
      (eComp (Complex A) (F.obj y) (F.obj (C.source b)) (F.obj z))
      (eComp (Complex A) (F.obj x) (F.obj y) (F.obj z))
      (F.map_comp x y (C.source b))
      (e_assoc' (Complex A) (F.obj x) (F.obj y)
        (F.obj (C.source b)) (F.obj z)).symm
      ((tensorZeroCochain (P.cochain b) (P.pathEvaluation w (C.target b) z)).comp
        (Cochain.ofHom (eComp (Complex A) (F.obj (C.source b))
          (F.obj (C.target b)) (F.obj z))) (zero_add 0))
    simpa only [pathEvaluation, prependMap, tensorHom_id] using h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
