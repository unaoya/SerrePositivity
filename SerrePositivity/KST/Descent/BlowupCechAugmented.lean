module

public import SerrePositivity.KST.Descent.BlowupCechColumns

/-!
# 抽象 blowup の四頂点の列と実際の増強 Čech nerve の同型

## 概要
各頂点の Čech 列の比較を、増強先まで含めた実際の増強単体対象の同型にまとめる。

## 方針
列全体の自然同型と指定増強の可換式を Comma の同型へ束ねる。

## 規約
各頂点の値の同型の寄せ集めではなく、全単体射と指定増強を保持する。

## 使われ方
論文 補題 3.3 の抽象 blowup 降下と Čech 降下を同じ前層・実際の Tot の図式に渡す。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent.AbstractBlowupSquare

variable {S : Scheme.{u}} [IsNoetherian S] (Q : AbstractBlowupSquare S)
  {V : FiniteTypeSchemes S} (cover : V ⟶ Q.square.X₄)

/-- 概要：抽象 blowup の一頂点の列と指定増強を増強単体対象にする（補題 3.3）。
方針：正方形の評価関手と自然な比較立方体の像を使う。
規約：元の頂点を増強先とする。使われ方：各頂点に元の被覆の実際の Čech 降下を適用する。 -/
noncomputable def cechColumnAugmented
    (evaluation : Square (FiniteTypeSchemes S) ⥤ FiniteTypeSchemes S) :
    SimplicialObject.Augmented (FiniteTypeSchemes S) where
  left := Q.cechBaseChangeSquares cover ⋙ evaluation
  right := evaluation.obj Q.square
  hom := Q.cechColumnAugmentation cover evaluation

/-- 概要：右上の列は実際の底変換被覆の増強 Čech nerve と同型（補題 3.3）。
方針：列の自然同型と増強の保存を同じ増強先の恒等同型と組み合わせる。
規約：元の変形先への指定増強を保つ。使われ方：右上の Čech 降下比較。 -/
noncomputable def cechColumn₂AugmentedIso :
    (Arrow.mk (finiteTypePullbackSnd cover Q.square.f₂₄)).augmentedCechNerve ≅
      Q.cechColumnAugmented cover Square.evaluation₂ :=
  Comma.isoMk (Q.cechColumn₂Iso cover) (Iso.refl Q.square.X₂)
    (by
      have hi : (Arrow.mk (finiteTypePullbackSnd cover Q.square.f₂₄)).augmentedCechNerve.hom ≫
          (SimplicialObject.const (FiniteTypeSchemes S)).map (𝟙 Q.square.X₂) =
            (Arrow.mk (finiteTypePullbackSnd cover Q.square.f₂₄)).augmentedCechNerve.hom :=
        (congrArg (_ ≫ ·) ((SimplicialObject.const (FiniteTypeSchemes S)).map_id _)).trans
          (Category.comp_id _)
      exact (Q.cechColumn₂Iso_augmentation cover).trans hi.symm)

/-- 概要：左下の列は実際の底変換被覆の増強 Čech nerve と同型（補題 3.3）。
方針：列の自然同型と増強の保存を同じ中心の恒等同型と組み合わせる。
規約：中心の厚みを保つ。使われ方：中心上の Čech 降下比較。 -/
noncomputable def cechColumn₃AugmentedIso :
    (Arrow.mk (finiteTypePullbackSnd cover Q.square.f₃₄)).augmentedCechNerve ≅
      Q.cechColumnAugmented cover Square.evaluation₃ :=
  Comma.isoMk (Q.cechColumn₃Iso cover) (Iso.refl Q.square.X₃)
    (by
      have hi : (Arrow.mk (finiteTypePullbackSnd cover Q.square.f₃₄)).augmentedCechNerve.hom ≫
          (SimplicialObject.const (FiniteTypeSchemes S)).map (𝟙 Q.square.X₃) =
            (Arrow.mk (finiteTypePullbackSnd cover Q.square.f₃₄)).augmentedCechNerve.hom :=
        (congrArg (_ ≫ ·) ((SimplicialObject.const (FiniteTypeSchemes S)).map_id _)).trans
          (Category.comp_id _)
      exact (Q.cechColumn₃Iso_augmentation cover).trans hi.symm)

/-- 概要：例外部分の列も実際の底変換被覆の増強 Čech nerve と同型（補題 3.3）。
方針：例外部分の自然比較を含む列の同型と増強の保存を組み合わせる。
規約：左上の Čech 性を追加の仮定にせず、実際の構成から得る。
使われ方：例外部分上の Čech 降下と自然な抽象 blowup の比較。 -/
noncomputable def cechColumn₁AugmentedIso :
    (Arrow.mk (finiteTypePullbackSnd cover
      (Q.square.f₁₃ ≫ Q.square.f₃₄))).augmentedCechNerve ≅
        Q.cechColumnAugmented cover Square.evaluation₁ :=
  Comma.isoMk (Q.cechColumn₁Iso cover) (Iso.refl Q.square.X₁)
    (by
      have hi : (Arrow.mk (finiteTypePullbackSnd cover
          (Q.square.f₁₃ ≫ Q.square.f₃₄))).augmentedCechNerve.hom ≫
          (SimplicialObject.const (FiniteTypeSchemes S)).map (𝟙 Q.square.X₁) =
            (Arrow.mk (finiteTypePullbackSnd cover
          (Q.square.f₁₃ ≫ Q.square.f₃₄))).augmentedCechNerve.hom :=
        (congrArg (_ ≫ ·) ((SimplicialObject.const (FiniteTypeSchemes S)).map_id _)).trans
          (Category.comp_id _)
      exact (Q.cechColumn₁Iso_augmentation cover).trans hi.symm)

/-- 概要：右下の列は元の被覆の指定された増強 Čech nerve と同型（補題 3.3）。
方針：元の列と同じ増強の定義を使う。
規約：基底の降下比較を別の射に置き換えない。
使われ方：四頂点の降下比較を同じ抽象 blowup 正方形で扱う。 -/
noncomputable def cechColumn₄AugmentedIso :
    (Arrow.mk cover).augmentedCechNerve ≅ Q.cechColumnAugmented cover Square.evaluation₄ :=
  Comma.isoMk (Iso.refl _) (Iso.refl Q.square.X₄)
    (by
      have hi : (Arrow.mk cover).augmentedCechNerve.hom ≫
          (SimplicialObject.const (FiniteTypeSchemes S)).map (𝟙 Q.square.X₄) =
            (Arrow.mk cover).augmentedCechNerve.hom :=
        (congrArg (_ ≫ ·) ((SimplicialObject.const (FiniteTypeSchemes S)).map_id _)).trans
          (Category.comp_id _)
      exact ((Category.id_comp _).trans (Q.cechColumnAugmentation₄_eq cover)).trans hi.symm)

end SerrePositivity.KST.Descent.AbstractBlowupSquare
