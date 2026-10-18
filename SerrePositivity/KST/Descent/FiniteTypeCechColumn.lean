module

public import SerrePositivity.KST.Descent.FiniteTypeBaseChangeComparison

/-!
# 指定底変換の Čech 列と底変換した被覆の実際の Čech nerve

## 概要
元の Čech 各段を指定モデルで底変換した列を、実際に底変換した被覆の Čech nerve と同定する。

## 方針
列全体の二射影が Cartesian であることを各段で検査し、Čech 底変換の標準比較を合成する。

## 規約
全単体射と増強先を保つ。前層が幾何的引き戻しを保存することは仮定しない。

## 使われ方
論文 補題 3.3 の抽象 blowup 各頂点の列へ、同じ被覆の Čech 降下を適用する幾何入力。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {X W Y : FiniteTypeSchemes S}
  (f : X ⟶ Y) (cover : W ⟶ Y)

/-- 概要：元の Čech 全段を指定モデルで底変換した実際の列（補題 3.3）。
方針：底変換 Arrow 関手の始域を取る。
規約：指定された finiteTypePullback の全単体射。使われ方：blowup 各頂点の列の同定。 -/
noncomputable def finiteTypeCechColumn : SimplicialObject (FiniteTypeSchemes S) :=
  (cechOverDiagram cover ⋙ finiteTypeOverBaseChangeArrow f) ⋙ Arrow.leftFunc

/-- 概要：底変換 Čech 列から底変換基底への指定増強（補題 3.3）。
方針：各段の指定第一射影を使う。
規約：底変換した被覆の基底は X。使われ方：Čech 降下の指定増強の比較。 -/
noncomputable def finiteTypeCechColumnFirst :
    finiteTypeCechColumn f cover ⟶ (SimplicialObject.const (FiniteTypeSchemes S)).obj X where
  app n := finiteTypePullbackFst f ((Arrow.mk cover).augmentedCechNerve.hom.app n)
  naturality {_ _} α := (finiteTypeBaseChangeMap_fst f ((cechOverDiagram cover).map α)).trans
    (Category.comp_id _).symm

/-- 概要：底変換 Čech 列から元の Čech 列への指定射影（補題 3.3）。
方針：各段の指定第二射影を使う。
規約：全単体射について自然。使われ方：元の前層の引き戻し比較との整合性。 -/
noncomputable def finiteTypeCechColumnSecond :
    finiteTypeCechColumn f cover ⟶ (Arrow.mk cover).cechNerve where
  app n := finiteTypePullbackSnd f ((Arrow.mk cover).augmentedCechNerve.hom.app n)
  naturality {_ _} α := finiteTypeBaseChangeMap_snd f ((cechOverDiagram cover).map α)

/-- 概要：指定底変換の Čech 列は図式全体で実際の引き戻し（補題 3.3）。
方針：全単体次数で指定 Cartesian 正方形を検査する。
規約：通常の幾何図式の普遍性であり Tot の交換ではない。
使われ方：底変換した被覆の Čech nerve との同じ二射影による比較。 -/
theorem finiteTypeCechColumn_isPullback :
    IsPullback (finiteTypeCechColumnFirst f cover) (finiteTypeCechColumnSecond f cover)
      ((SimplicialObject.const (FiniteTypeSchemes S)).map f)
      (Arrow.mk cover).augmentedCechNerve.hom :=
  IsPullback.of_forall_isPullback_app fun n ↦
    finiteTypePullback_isPullback f ((Arrow.mk cover).augmentedCechNerve.hom.app n)

/-- 概要：選択された底変換被覆の Čech nerve と指定底変換列の自然同型（補題 3.3）。
方針：二つの図式全体の Cartesian 正方形の標準同型を使う。
規約：増強と元の Čech への比較を同時に保持。使われ方：指定モデルの列の Čech 性の同定。 -/
noncomputable def finiteTypeCechColumnCanonicalIso :
    (Arrow.mk (pullback.snd cover f)).cechNerve ≅ finiteTypeCechColumn f cover :=
  (baseChangeCech_isPullback cover f).flip.isoIsPullback _ _
    (finiteTypeCechColumn_isPullback f cover)

/-- 概要：列の標準比較は底変換基底への増強を保つ（補題 3.3）。
方針：二つの Cartesian 正方形の標準同型の第一射影公式。
規約：同じ指定増強。使われ方：増強先を含む降下比較の同定。 -/
@[reassoc] theorem finiteTypeCechColumnCanonicalIso_hom_first :
    (finiteTypeCechColumnCanonicalIso f cover).hom ≫ finiteTypeCechColumnFirst f cover =
      (Arrow.mk (pullback.snd cover f)).augmentedCechNerve.hom :=
  (baseChangeCech_isPullback cover f).flip.isoIsPullback_hom_fst _ _
    (finiteTypeCechColumn_isPullback f cover)

/-- 概要：列の標準比較は元の Čech への指定射を保つ（補題 3.3）。
方針：二つの Cartesian 正方形の標準同型の第二射影公式。
規約：同じ元の被覆。使われ方：前層を適用した後の比較の自然性。 -/
@[reassoc] theorem finiteTypeCechColumnCanonicalIso_hom_second :
    (finiteTypeCechColumnCanonicalIso f cover).hom ≫ finiteTypeCechColumnSecond f cover =
      Arrow.mapCechNerve (baseChangeArrowToOriginal cover f) :=
  (baseChangeCech_isPullback cover f).flip.isoIsPullback_hom_snd _ _
    (finiteTypeCechColumn_isPullback f cover)

/-- 概要：実際の指定底変換被覆の Čech nerve と指定底変換列の自然同型（補題 3.3）。
方針：指定底変換 Arrow の標準同型を Čech nerve で写し、列の標準比較に合成する。
規約：元の有限型の圏内の実際の被覆を使う。
使われ方：blowup 各頂点の列に元の被覆の底変換の Čech 降下を適用する。 -/
noncomputable def finiteTypeCechColumnIso :
    (Arrow.mk (finiteTypePullbackSnd cover f)).cechNerve ≅ finiteTypeCechColumn f cover :=
  (SimplicialObject.cechNerve (C := FiniteTypeSchemes S)).mapIso
    (finiteTypeBaseChangeArrowIso cover (Over.mk f)) ≪≫ finiteTypeCechColumnCanonicalIso f cover

set_option backward.isDefEq.respectTransparency false in
/-- 概要：実際の指定底変換被覆との比較は増強先を含めて可換（補題 3.3）。
方針：列の第一射影公式と Arrow の Čech 比較の増強の可換性を合成する。
規約：対象の同型だけではなく指定された増強を保持する。
使われ方：同じ前層の実際の降下比較を正方形の列へ移す。 -/
theorem finiteTypeCechColumnIso_augmentation :
    (finiteTypeCechColumnIso f cover).hom ≫ finiteTypeCechColumnFirst f cover =
      (Arrow.mk (finiteTypePullbackSnd cover f)).augmentedCechNerve.hom := by
  let α := (finiteTypeBaseChangeArrowIso cover (Over.mk f)).hom
  change (Arrow.mapCechNerve α ≫ (finiteTypeCechColumnCanonicalIso f cover).hom) ≫
    finiteTypeCechColumnFirst f cover = _
  rw [Category.assoc, finiteTypeCechColumnCanonicalIso_hom_first]
  exact (mapCechNerve_augmentation α).trans
    ((congrArg (_ ≫ ·) ((SimplicialObject.const (FiniteTypeSchemes S)).map_id _)).trans
      (Category.comp_id _))

set_option backward.isDefEq.respectTransparency false in
/-- 概要：実際の指定底変換被覆との比較は元の Čech への指定射も保つ（補題 3.3）。
方針：列の第二射影公式と Arrow の標準比較の第一射影公式を使う。
規約：元の整数群への比較に使う幾何射を保持する。
使われ方：全単体射と元の前層の自然性を同時に扱う。 -/
theorem finiteTypeCechColumnIso_toOriginal :
    (finiteTypeCechColumnIso f cover).hom ≫ finiteTypeCechColumnSecond f cover =
      Arrow.mapCechNerve ((finiteTypeOverBaseChangeToOriginal cover).app (Over.mk f)) := by
  let α := (finiteTypeBaseChangeArrowIso cover (Over.mk f)).hom
  let β := baseChangeArrowToOriginal cover f
  let γ := (finiteTypeOverBaseChangeToOriginal cover).app (Over.mk f)
  have h : α ≫ β = γ := by
    apply Arrow.hom_ext
    · exact finiteTypeBaseChangeIso_hom_fst cover (Over.mk f)
    · exact Category.id_comp _
  change (Arrow.mapCechNerve α ≫ (finiteTypeCechColumnCanonicalIso f cover).hom) ≫
    finiteTypeCechColumnSecond f cover = Arrow.mapCechNerve γ
  rw [Category.assoc, finiteTypeCechColumnCanonicalIso_hom_second]
  exact ((SimplicialObject.cechNerve (C := FiniteTypeSchemes S)).map_comp α β).symm.trans
    (congrArg (fun k ↦ Arrow.mapCechNerve k) h)

end SerrePositivity.KST.Descent
