module

public import SerrePositivity.KST.Descent.BlowupBaseChangeFunctor
public import SerrePositivity.KST.Descent.FiniteTypeCechColumn

/-!
# 抽象 blowup の全頂点の Čech 列の実際の同定

## 概要
底変換した抽象 blowup の四頂点の列を、元の被覆の底変換の実際の Čech nerve と比較する。

## 方針
右上と左下は指定モデルの列を使い、左上は例外部分の標準同型の自然性を二射影で検査する。

## 規約
全単体射と指定増強を保持する。値域の Tot の交換や前層の引き戻し保存は仮定しない。

## 使われ方
論文 補題 3.3 の抽象 blowup 降下と同じ被覆の Čech 降下の比較。
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：正方形の射は左上から右下への合成構造射も保つ（補題 3.3）。
方針：左辺・下辺の二つの可換式を合成する。
規約：実際の射の等式。使われ方：例外部分の Čech 列の第二射影の自然性。 -/
theorem square_hom_comm₁₄ {C : Type u} [Category.{v} C] {Q R : Square C} (a : Q ⟶ R) :
    a.τ₁ ≫ (R.f₁₃ ≫ R.f₃₄) = (Q.f₁₃ ≫ Q.f₃₄) ≫ a.τ₄ := by
  rw [← Category.assoc, ← a.comm₁₃, Category.assoc, ← a.comm₃₄, ← Category.assoc]

namespace AbstractBlowupSquare

variable {S : Scheme.{u}} [IsNoetherian S] (Q : AbstractBlowupSquare S)
  {V : FiniteTypeSchemes S} (cover : V ⟶ Q.square.X₄)

/-- 概要：右上の Čech 列は固有射による指定底変換列そのもの（補題 3.3）。
方針：構成の対象と map の定義を使う。
規約：全単体射を含む関手の等式。使われ方：右上で同じ被覆の Čech 降下を使う。 -/
theorem cechColumn₂_eq :
    Q.cechBaseChangeSquares cover ⋙ Square.evaluation₂ = finiteTypeCechColumn Q.square.f₂₄ cover :=
  rfl

/-- 概要：左下の Čech 列は閉中心による指定底変換列そのもの（補題 3.3）。
方針：構成の対象と map の定義を使う。
規約：中心の厚みも保持。使われ方：中心上で同じ被覆の Čech 降下を使う。 -/
theorem cechColumn₃_eq :
    Q.cechBaseChangeSquares cover ⋙ Square.evaluation₃ = finiteTypeCechColumn Q.square.f₃₄ cover :=
  rfl

/-- 概要：右下の Čech 列は元の被覆の Čech nerve そのもの（補題 3.3）。
方針：基底の対象と map の定義を使う。
規約：元の指定被覆を変更しない。使われ方：元の降下比較の固定。 -/
theorem cechColumn₄_eq :
    Q.cechBaseChangeSquares cover ⋙ Square.evaluation₄ = (Arrow.mk cover).cechNerve := rfl

set_option backward.isDefEq.respectTransparency false in
/-- 概要：例外部分の指定底変換との標準同型は全基底射に自然（補題 3.3）。
方針：比較立方体の自然性と例外部分の構造射の可換性を二射影で検査する。
規約：Čech 段ごとに独立な同型を選ばない。
使われ方：例外部分の Čech 列の自然同型を元の Over の段階で供給する。 -/
theorem baseChangeExceptionalIso_naturality {Z Z' : Over Q.square.X₄} (k : Z ⟶ Z') :
    (Q.baseChangeMap k).τ₁ ≫ (Q.baseChangeExceptionalIso Z'.hom).hom =
      (Q.baseChangeExceptionalIso Z.hom).hom ≫
        finiteTypeBaseChangeMap (Q.square.f₁₃ ≫ Q.square.f₃₄) k := by
  let h := Z.hom
  let h' := Z'.hom
  let e := Q.baseChangeExceptionalIso h
  let e' := Q.baseChangeExceptionalIso h'
  change (Q.baseChangeMap k).τ₁ ≫ e'.hom =
    e.hom ≫ finiteTypeBaseChangeMap (Q.square.f₁₃ ≫ Q.square.f₃₄) k
  apply (finiteTypePullback_isPullback (Q.square.f₁₃ ≫ Q.square.f₃₄) h').hom_ext
  · have hn : (Q.baseChangeMap k).τ₁ ≫ (Q.baseChangeCube h').τ₁ =
        (Q.baseChangeCube h).τ₁ :=
      (congrArg (fun a ↦ a.τ₁) (Q.baseChangeToOriginal.naturality k)).trans
        (Category.comp_id _)
    have hl : ((Q.baseChangeMap k).τ₁ ≫ e'.hom) ≫
        finiteTypePullbackFst (Q.square.f₁₃ ≫ Q.square.f₃₄) h' =
          (Q.baseChangeMap k).τ₁ ≫ (Q.baseChangeCube h').τ₁ :=
      (Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (Q.baseChangeExceptionalIso_hom_fst h'))
    have hr : (e.hom ≫ finiteTypeBaseChangeMap (Q.square.f₁₃ ≫ Q.square.f₃₄) k) ≫
        finiteTypePullbackFst (Q.square.f₁₃ ≫ Q.square.f₃₄) h' =
          (Q.baseChangeCube h).τ₁ :=
      (Category.assoc _ _ _).trans
        ((congrArg (e.hom ≫ ·)
          (finiteTypeBaseChangeMap_fst (Q.square.f₁₃ ≫ Q.square.f₃₄) k)).trans
            (Q.baseChangeExceptionalIso_hom_fst h))
    exact hl.trans (hn.trans hr.symm)
  · have hl : ((Q.baseChangeMap k).τ₁ ≫ e'.hom) ≫
        finiteTypePullbackSnd (Q.square.f₁₃ ≫ Q.square.f₃₄) h' =
          (Q.baseChangeMap k).τ₁ ≫
            ((Q.baseChange h').square.f₁₃ ≫ (Q.baseChange h').square.f₃₄) :=
      (Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (Q.baseChangeExceptionalIso_hom_snd h'))
    have hr : (e.hom ≫ finiteTypeBaseChangeMap (Q.square.f₁₃ ≫ Q.square.f₃₄) k) ≫
        finiteTypePullbackSnd (Q.square.f₁₃ ≫ Q.square.f₃₄) h' =
          ((Q.baseChange h).square.f₁₃ ≫ (Q.baseChange h).square.f₃₄) ≫ k.left :=
      (Category.assoc _ _ _).trans
        ((congrArg (e.hom ≫ ·)
          (finiteTypeBaseChangeMap_snd (Q.square.f₁₃ ≫ Q.square.f₃₄) k)).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (· ≫ k.left) (Q.baseChangeExceptionalIso_hom_snd h))))
    exact hl.trans ((square_hom_comm₁₄ (Q.baseChangeMap k)).trans hr.symm)

/-- 概要：例外部分の指定底変換との標準同型を Over 全体の自然同型にする（補題 3.3）。
方針：全基底射に関する自然性を使う。
規約：各 Čech 図式への制限前から一つの自然比較を保持する。
使われ方：例外部分の列とその増強の比較。 -/
noncomputable def baseChangeExceptionalNatIso :
    Q.baseChangeFunctor ⋙ Square.evaluation₁ ≅
      finiteTypeOverBaseChangeArrow (Q.square.f₁₃ ≫ Q.square.f₃₄) ⋙ Arrow.leftFunc :=
  NatIso.ofComponents (fun Z ↦ Q.baseChangeExceptionalIso Z.hom)
    (fun {_ _} α ↦ Q.baseChangeExceptionalIso_naturality α)

set_option backward.isDefEq.respectTransparency false in
/-- 概要：例外部分の全 Čech 列と元の例外部分の指定底変換列の自然同型（補題 3.3）。
方針：全基底射に関する標準同型の自然性を元の Čech 図式へ制限する。
規約：段ごとの対象同型だけに弱めず、全単体射を保持する。
使われ方：例外部分の列を実際の底変換被覆の Čech nerve へ接続する。 -/
noncomputable def cechExceptionalColumnIso :
    Q.cechBaseChangeSquares cover ⋙ Square.evaluation₁ ≅
      finiteTypeCechColumn (Q.square.f₁₃ ≫ Q.square.f₃₄) cover :=
  Functor.isoWhiskerLeft (cechOverDiagram cover) Q.baseChangeExceptionalNatIso

/-- 概要：右上の列は実際に底変換した元の被覆の Čech nerve と自然同型（補題 3.3）。
方針：指定底変換列の標準同型を使う。
規約：元の固有射そのものによる底変換。使われ方：右上の Čech 降下比較。 -/
noncomputable def cechColumn₂Iso :
    (Arrow.mk (finiteTypePullbackSnd cover Q.square.f₂₄)).cechNerve ≅
      Q.cechBaseChangeSquares cover ⋙ Square.evaluation₂ :=
  finiteTypeCechColumnIso Q.square.f₂₄ cover

/-- 概要：左下の列は実際に底変換した元の被覆の Čech nerve と自然同型（補題 3.3）。
方針：指定底変換列の標準同型を使う。
規約：元の閉中心を被約化しない。使われ方：中心上の Čech 降下比較。 -/
noncomputable def cechColumn₃Iso :
    (Arrow.mk (finiteTypePullbackSnd cover Q.square.f₃₄)).cechNerve ≅
      Q.cechBaseChangeSquares cover ⋙ Square.evaluation₃ :=
  finiteTypeCechColumnIso Q.square.f₃₄ cover

/-- 概要：左上の列は元の例外部分へ底変換した被覆の実際の Čech nerve と自然同型（補題 3.3）。
方針：指定底変換列の比較と例外部分の自然同型の逆を合成する。
規約：全単体射を保持し、左上の列の Čech 性を仮定しない。
使われ方：例外部分上の Čech 降下比較。 -/
noncomputable def cechColumn₁Iso :
    (Arrow.mk (finiteTypePullbackSnd cover (Q.square.f₁₃ ≫ Q.square.f₃₄))).cechNerve ≅
      Q.cechBaseChangeSquares cover ⋙ Square.evaluation₁ :=
  finiteTypeCechColumnIso (Q.square.f₁₃ ≫ Q.square.f₃₄) cover ≪≫
    (Q.cechExceptionalColumnIso cover).symm

/-- 概要：底変換された正方形の列から元の頂点への指定増強（補題 3.3）。
方針：正方形の自然な比較立方体を指定した評価関手で写す。
規約：全単体射に自然。使われ方：各頂点の実際の Čech 降下比較の固定。 -/
noncomputable def cechColumnAugmentation
    (evaluation : Square (FiniteTypeSchemes S) ⥤ FiniteTypeSchemes S) :
    Q.cechBaseChangeSquares cover ⋙ evaluation ⟶
      (SimplicialObject.const (FiniteTypeSchemes S)).obj (evaluation.obj Q.square) where
  app n := evaluation.map ((Q.cechBaseChangeToOriginal cover).app n)
  naturality {n m} α := by
    have hn : (Q.cechBaseChangeSquares cover).map α ≫
        (Q.cechBaseChangeToOriginal cover).app m =
          (Q.cechBaseChangeToOriginal cover).app n :=
      ((Q.cechBaseChangeToOriginal cover).naturality α).trans (Category.comp_id _)
    exact (evaluation.map_comp _ _).symm.trans
      ((congrArg evaluation.map hn).trans (Category.comp_id _).symm)

/-- 概要：右上の列の指定増強は元の変形先への第一射影（補題 3.3）。
方針：比較立方体の定義を使う。
規約：全単体次数の自然変換の等式。使われ方：実際の Čech 降下比較との一致。 -/
theorem cechColumnAugmentation₂_eq :
    Q.cechColumnAugmentation cover Square.evaluation₂ =
      finiteTypeCechColumnFirst Q.square.f₂₄ cover := rfl

/-- 概要：左下の列の指定増強は元の中心への第一射影（補題 3.3）。
方針：比較立方体の定義を使う。
規約：元の中心を変更しない。使われ方：中心上の実際の Čech 降下比較との一致。 -/
theorem cechColumnAugmentation₃_eq :
    Q.cechColumnAugmentation cover Square.evaluation₃ =
      finiteTypeCechColumnFirst Q.square.f₃₄ cover := rfl

/-- 概要：右下の列の指定増強は元の被覆の実際の増強（補題 3.3）。
方針：比較立方体の基底の定義を使う。
規約：元の降下比較の射そのもの。使われ方：抽象 blowup の比較の基底側。 -/
theorem cechColumnAugmentation₄_eq :
    Q.cechColumnAugmentation cover Square.evaluation₄ =
      (Arrow.mk cover).augmentedCechNerve.hom := rfl

/-- 概要：例外部分の列の標準同型は元の例外部分への増強を保つ（補題 3.3）。
方針：各段で例外部分の標準同型の第一射影公式を使う。
規約：全単体次数の自然変換の等式。使われ方：左上の列の指定降下比較。 -/
theorem cechExceptionalColumnIso_augmentation :
    (Q.cechExceptionalColumnIso cover).hom ≫
        finiteTypeCechColumnFirst (Q.square.f₁₃ ≫ Q.square.f₃₄) cover =
      Q.cechColumnAugmentation cover Square.evaluation₁ := by
  apply NatTrans.ext
  funext n
  exact Q.baseChangeExceptionalIso_hom_fst ((Arrow.mk cover).augmentedCechNerve.hom.app n)

/-- 概要：右上の実際の Čech 比較は増強先まで同じ（補題 3.3）。
方針：指定底変換列の比較の増強公式を使う。
規約：変形先への指定降下比較。使われ方：同じ前層による Čech 降下の移送。 -/
theorem cechColumn₂Iso_augmentation :
    (Q.cechColumn₂Iso cover).hom ≫ Q.cechColumnAugmentation cover Square.evaluation₂ =
      (Arrow.mk (finiteTypePullbackSnd cover Q.square.f₂₄)).augmentedCechNerve.hom :=
  finiteTypeCechColumnIso_augmentation Q.square.f₂₄ cover

/-- 概要：左下の実際の Čech 比較は増強先まで同じ（補題 3.3）。
方針：指定底変換列の比較の増強公式を使う。
規約：元の中心への指定降下比較。使われ方：中心上の同じ前層の Čech 降下の移送。 -/
theorem cechColumn₃Iso_augmentation :
    (Q.cechColumn₃Iso cover).hom ≫ Q.cechColumnAugmentation cover Square.evaluation₃ =
      (Arrow.mk (finiteTypePullbackSnd cover Q.square.f₃₄)).augmentedCechNerve.hom :=
  finiteTypeCechColumnIso_augmentation Q.square.f₃₄ cover

/-- 概要：例外部分の実際の Čech 比較も増強先まで同じ（補題 3.3）。
方針：例外部分の自然同型の逆と指定底変換列の増強公式を合成する。
規約：左上の列の同型だけを仮定せず、指定された降下比較の射を保つ。
使われ方：抽象 blowup の四頂点における同じ被覆の Čech 降下比較。 -/
theorem cechColumn₁Iso_augmentation :
    (Q.cechColumn₁Iso cover).hom ≫ Q.cechColumnAugmentation cover Square.evaluation₁ =
      (Arrow.mk (finiteTypePullbackSnd cover
        (Q.square.f₁₃ ≫ Q.square.f₃₄))).augmentedCechNerve.hom := by
  let A := finiteTypeCechColumnIso (Q.square.f₁₃ ≫ Q.square.f₃₄) cover
  let E := Q.cechExceptionalColumnIso cover
  have hE : E.inv ≫ Q.cechColumnAugmentation cover Square.evaluation₁ =
      finiteTypeCechColumnFirst (Q.square.f₁₃ ≫ Q.square.f₃₄) cover :=
    (congrArg (E.inv ≫ ·) (Q.cechExceptionalColumnIso_augmentation cover).symm).trans
      (Iso.inv_hom_id_assoc E _)
  exact (Category.assoc _ _ _).trans
    ((congrArg (A.hom ≫ ·) hE).trans
      (finiteTypeCechColumnIso_augmentation (Q.square.f₁₃ ≫ Q.square.f₃₄) cover))

end AbstractBlowupSquare

end SerrePositivity.KST.Descent
