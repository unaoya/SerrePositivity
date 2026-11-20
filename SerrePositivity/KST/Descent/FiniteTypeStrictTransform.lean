module

public import SerrePositivity.KST.Descent.FiniteFlatStrictTransform
public import SerrePositivity.KST.Descent.FiniteTypeLimits
public import SerrePositivity.KST.Descent.ClosedCenterSquare
public import SerrePositivity.KST.Descent.CechRefinementHomotopy

/-!
# 元の有限型の圏内の blowup と strict transform

## 概要
平坦化後の有限忠実平坦な細分を、元の前層の定義域と実際の Čech 比較へ持ち上げる。

## 方針
実際の blowup・strict transform・二つの構造射を同じ基底 S 上へ持ち上げる。

## 規約
元の射の有限性と基底の Noether 性を明示する。平坦化の存在は主張しない。

## 使われ方
論文 補題 3.3 の有限平坦細分を、補題 3.2 の Čech 計算に接続する幾何入力。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SerrePositivity.KST.SchemeLemmas

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S]

/-- 概要：有限型対象の実際の blowup を同じ有限型の圏へ持ち上げる（補題 3.3）。
方針：Noether 基底上の blowup の固有性と元の構造射の有限型性を合成する。
規約：underlying scheme は実際の blowup。
使われ方：平坦化後も前層の定義域を変更しない。 -/
noncomputable def finiteTypeBlowup (Y : FiniteTypeSchemes S) (J : Y.obj.left.IdealSheafData) :
    FiniteTypeSchemes S := by
  have : LocallyOfFiniteType Y.obj.hom := Y.property.1
  have : QuasiCompact Y.obj.hom := Y.property.2
  exact ⟨Over.mk (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J ≫ Y.obj.hom),
    locallyOfFiniteType_comp _ _, quasiCompact_comp _ _⟩

/-- 概要：実際の blowup 構造射を同じ基底上へ持ち上げる（補題 3.3）。
方針：対象の構造射を blowup 構造射で定義したことを使う。
規約：指定された射そのものを使う。
使われ方：元の有限射を底変換する幾何的な射。 -/
noncomputable def finiteTypeBlowupProjection (Y : FiniteTypeSchemes S)
    (J : Y.obj.left.IdealSheafData) : finiteTypeBlowup Y J ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J))

variable {X Y : FiniteTypeSchemes S} (f : X ⟶ Y)
  (U : Y.obj.left.Opens) (J : Y.obj.left.IdealSheafData) [IsFinite f.hom.left]

set_option backward.isDefEq.respectTransparency false in
/-- 概要：有限射の実際の strict transform を元の有限型の圏へ持ち上げる（補題 3.3）。
方針：有限な構造射を blowup の有限型な構造射と合成する。
規約：underlying scheme と開部分は元の実際の strict transform。
使われ方：平坦化後の有限平坦射の始域。 -/
noncomputable def finiteTypeStrictTransform : FiniteTypeSchemes S := by
  have := strictTransformπ_isFinite f.hom.left U J
  have : LocallyOfFiniteType (finiteTypeBlowup Y J).obj.hom :=
    (finiteTypeBlowup Y J).property.1
  have : QuasiCompact (finiteTypeBlowup Y J).obj.hom :=
    (finiteTypeBlowup Y J).property.2
  exact ⟨Over.mk (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ f.hom.left U J ≫ (finiteTypeBlowup Y J).obj.hom),
    locallyOfFiniteType_comp _ _, quasiCompact_comp _ _⟩

/-- 概要：strict transform から blowup への指定射（補題 3.3）。
方針：実際の構造射を Over の射へ持ち上げる。
規約：元の有限型の圏内の射。
使われ方：平坦化後の有限忠実平坦な被覆。 -/
noncomputable def finiteTypeStrictTransformProjection :
    finiteTypeStrictTransform f U J ⟶ finiteTypeBlowup Y J :=
  ObjectProperty.homMk (Over.homMk (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ f.hom.left U J))

/-- 概要：strict transform から元の始域への指定射（補題 3.3）。
方針：実際の二射影の可換式と元の基底上の可換式を合成する。
規約：全て同じ S 上の射。
使われ方：平坦被覆から元の被覆への細分。 -/
noncomputable def finiteTypeStrictTransformToOriginal : finiteTypeStrictTransform f U J ⟶ X :=
  ObjectProperty.homMk (Over.homMk (_root_.SerrePositivity.AlgebraicGeometry.strictTransformToOriginal f.hom.left U J) (by
    change _root_.SerrePositivity.AlgebraicGeometry.strictTransformToOriginal f.hom.left U J ≫ X.obj.hom =
      _root_.SerrePositivity.AlgebraicGeometry.strictTransformπ f.hom.left U J ≫ (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J ≫ Y.obj.hom)
    exact (congrArg (_ ≫ ·) f.hom.w.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ Y.obj.hom) (_root_.SerrePositivity.AlgebraicGeometry.strictTransform_square f.hom.left U J)).trans
          (Category.assoc _ _ _)))))

/-- 概要：strict transform の指定四辺は有限型の圏内で可換（補題 3.3）。
方針：充満部分圏と Over を忘れて実際の二射影の式を使う。
規約：実際の前層を適用できる射の等式。
使われ方：引き戻しへの細分射の構成。 -/
theorem finiteTypeStrictTransform_comm :
    finiteTypeStrictTransformToOriginal f U J ≫ f =
      finiteTypeStrictTransformProjection f U J ≫ finiteTypeBlowupProjection Y J := by
  apply ObjectProperty.hom_ext
  apply (Over.forget S).map_injective
  exact _root_.SerrePositivity.AlgebraicGeometry.strictTransform_square f.hom.left U J

/-- 概要：有限型の圏内の strict transform の構造射は有限（補題 3.3）。
方針：underlying scheme の有限性をそのまま使う。
規約：圏を持ち上げても射の性質を弱めない。
使われ方：有限平坦 transfer の適用対象。 -/
theorem finiteTypeStrictTransformProjection_isFinite :
    IsFinite (finiteTypeStrictTransformProjection f U J).hom.left :=
  strictTransformπ_isFinite f.hom.left U J

/-- 概要：中心外からの strict transform の指定射は全射（補題 3.3）。
方針：実際の blowup 上の全射性を同じ指定射へ移す。
規約：元の有限射の全射性を要求する。
使われ方：平坦化後の射を忠実平坦な被覆として使う。 -/
theorem finiteTypeStrictTransformProjection_surjective [Surjective f.hom.left] :
    Surjective (finiteTypeStrictTransformProjection f (_root_.SerrePositivity.AlgebraicGeometry.centerComplement J) J).hom.left :=
  strictTransformπ_centerComplement_surjective f.hom.left J

/-- 概要：strict transform を元の射の実際の底変換へ写す細分射（補題 3.3）。
方針：有限型の圏内の指定引き戻しの普遍性に二つの構造射を入れる。
規約：元の有限型の圏と指定引き戻しを使用する。
使われ方：平坦化後の Čech 被覆の細分比較。 -/
noncomputable def finiteTypeStrictTransformToPullback :
    finiteTypeStrictTransform f U J ⟶ finiteTypePullback f (finiteTypeBlowupProjection Y J) :=
  (finiteTypePullback_isPullback f (finiteTypeBlowupProjection Y J)).lift
    (finiteTypeStrictTransformToOriginal f U J) (finiteTypeStrictTransformProjection f U J)
    (finiteTypeStrictTransform_comm f U J)

/-- 概要：細分射は blowup 基底上の射（補題 3.3）。
方針：引き戻しへの lift の第二射影公式を使う。
規約：前層による比較に使う指定可換式。
使われ方：実際の Čech 細分比較。 -/
theorem finiteTypeStrictTransformToPullback_snd :
    finiteTypeStrictTransformToPullback f U J ≫
        finiteTypePullbackSnd f (finiteTypeBlowupProjection Y J) =
      finiteTypeStrictTransformProjection f U J :=
  (finiteTypePullback_isPullback f (finiteTypeBlowupProjection Y J)).lift_snd _ _ _

/-- 概要：平坦化後の被覆から元の底変換被覆への実際の Čech 比較（補題 3.3）。
方針：構成した有限型の圏内の細分射に Čech nerve 関手を適用する。
規約：全ての単体次数と面射・退化射を保持する。比較の降下性は別途証明する。
使われ方：原典の τ 位相の細分を Čech 計算に置換する幾何入力。 -/
noncomputable def finiteTypeStrictTransformCechRefinement :
    (Arrow.mk (finiteTypeStrictTransformProjection f U J)).cechNerve ⟶
      (Arrow.mk (finiteTypePullbackSnd f (finiteTypeBlowupProjection Y J))).cechNerve :=
  refinementCechMap _ _ (finiteTypeStrictTransformToPullback f U J)
    (finiteTypeStrictTransformToPullback_snd f U J)

/-- 概要：実際の Čech 細分比較は指定増強を保つ（論文 補題 3.3）。
方針：同じ Arrow の射が与える増強 Čech の可換性と、基底の恒等射保存を使う。
規約：増強先は blowup の同じ有限型対象。
使われ方：細分の比較を Tot の降下比較の矢として扱う。 -/
theorem finiteTypeStrictTransformCechRefinement_augmentation :
    finiteTypeStrictTransformCechRefinement f U J ≫
        (Arrow.mk (finiteTypePullbackSnd f
          (finiteTypeBlowupProjection Y J))).augmentedCechNerve.hom =
      (Arrow.mk (finiteTypeStrictTransformProjection f U J)).augmentedCechNerve.hom := by
  let α : Arrow.mk (finiteTypeStrictTransformProjection f U J) ⟶
      Arrow.mk (finiteTypePullbackSnd f (finiteTypeBlowupProjection Y J)) :=
    Arrow.homMk (finiteTypeStrictTransformToPullback f U J) (𝟙 _)
      ((finiteTypeStrictTransformToPullback_snd f U J).trans (Category.comp_id _).symm)
  have h := (Arrow.mapAugmentedCechNerve α).w
  exact h.trans
    ((congrArg (_ ≫ ·) ((SimplicialObject.const (FiniteTypeSchemes S)).map_id _)).trans
      (Category.comp_id _))

/-- 概要：平坦化後の指定射は元の有限型の圏内の有限忠実平坦な有限表示被覆（補題 3.3）。
方針：実際の構造射の平坦性と、既に証明した有限性・全射性・有限表示性を合わせる。
規約：平坦性は実際の strict transform についての入力で、中心の存在は別工程。
使われ方：同じ前層と Čech 比較への有限平坦 transfer の適用。 -/
theorem finiteTypeStrictTransform_flatCover [Surjective f.hom.left]
    [Flat (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ f.hom.left (_root_.SerrePositivity.AlgebraicGeometry.centerComplement J) J)] :
    IsFinite (finiteTypeStrictTransformProjection f (_root_.SerrePositivity.AlgebraicGeometry.centerComplement J) J).hom.left ∧
      Flat (finiteTypeStrictTransformProjection f (_root_.SerrePositivity.AlgebraicGeometry.centerComplement J) J).hom.left ∧
      Surjective (finiteTypeStrictTransformProjection f (_root_.SerrePositivity.AlgebraicGeometry.centerComplement J) J).hom.left ∧
      LocallyOfFinitePresentation
        (finiteTypeStrictTransformProjection f (_root_.SerrePositivity.AlgebraicGeometry.centerComplement J) J).hom.left :=
  ⟨strictTransformπ_isFinite f.hom.left _ J,
    (inferInstance : Flat (_root_.SerrePositivity.AlgebraicGeometry.strictTransformπ f.hom.left (_root_.SerrePositivity.AlgebraicGeometry.centerComplement J) J)),
    strictTransformπ_centerComplement_surjective f.hom.left J,
    strictTransformπ_locallyOfFinitePresentation f.hom.left _ J⟩

/-- 概要：実際の blowup を同じ有限型の圏の抽象 blowup 正方形にする（補題 3.3）。
方針：中心の台を被約閉中心とし、その実際の引き戻し・固有性・中心外同型を使う。
規約：中心の冪零構造を保存する主張ではない。抽象 blowup の幾何条件を全て検査する。
使われ方：平坦化中心に実降下の公理 (2) と中心上の帰納を適用する。 -/
noncomputable def finiteTypeBlowupSquare (Y : FiniteTypeSchemes S)
    (J : Y.obj.left.IdealSheafData) : AbstractBlowupSquare S := by
  have : IsProper (finiteTypeBlowupProjection Y J).hom.left :=
    inferInstanceAs (IsProper (_root_.SerrePositivity.AlgebraicGeometry.blowupπ J))
  exact abstractBlowupOfReducedCenter (finiteTypeBlowupProjection Y J) J.support
    (_root_.SerrePositivity.AlgebraicGeometry.blowupπ_restrict_complement_isIso J)

end SerrePositivity.KST.Descent
