module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupAffine
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
概要：KST §5 の一般スキーム上の blowup の分離性と固有性。
方針：各アフィン開集合上の Rees Proj との同型を用いて標的局所的に確認する。
規約：固有性には切断中心の有限生成性を仮定し、局所 Noether 基底では自動化する。
使われ方：古典的 blowup 正方形と Stacks 081T の平坦化への入力。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {X : Scheme.{u}} (I : X.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/--
概要：一般のイデアル層に沿う通常の blowup の構造射は分離。
方針：全アフィン開集合上で Proj の分離性へ帰着する。
規約：KST §5、中心の有限生成性は不要。
使われ方：比較射の一意性と古典的スキーム射の議論。
-/
instance blowupπ_isSeparated : IsSeparated (blowupπ I) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun U : X.affineOpens => U.1) (iSup_affineOpens_eq_top X)
  intro U
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsSeparated (blowupAffineIso I U).hom,
    blowupAffineIso_hom_restrict]
  unfold affineBlowupModelπ
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
概要：各アフィン開集合上で中心が有限生成なら blowup の構造射は固有。
方針：アフィン上の Rees Proj の固有性を標的局所的に貼り合わせる。
規約：KST §5、仮定は中心イデアルの有限生成性そのもの。
使われ方：有限型中心の blowup の幾何学的入力。
-/
theorem blowupπ_isProper (hI : ∀ U : X.affineOpens, (I.ideal U).FG) :
    IsProper (blowupπ I) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun U : X.affineOpens => U.1) (iSup_affineOpens_eq_top X)
  intro U
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsProper (blowupAffineIso I U).hom,
    blowupAffineIso_hom_restrict]
  unfold affineBlowupModelπ
  have := affineBlowupπ_isProper (I.ideal U) (hI U)
  infer_instance

/--
概要：局所 Noether スキームの任意のイデアル層の通常の blowup は固有。
方針：アフィン切断環の Noether 性から中心イデアルの有限生成性を得る。
規約：KST §5、基底の準コンパクト性は不要。
使われ方：Stacks 081T の Noether 特殊形への入力。
-/
instance blowupπ_isProper_of_isLocallyNoetherian [IsLocallyNoetherian X] :
    IsProper (blowupπ I) := by
  apply blowupπ_isProper I
  intro U
  have := IsLocallyNoetherian.component_noetherian U
  exact Ideal.fg_of_isNoetherianRing (I.ideal U)

/--
概要：Noether 基底の通常の blowup も Noether スキーム。
方針：固有性から有限型性と準コンパクト性を得て、局所 Noether 性とコンパクト性を移す。
規約：KST §5、Stacks 081T の最初の基底変更。
使われ方：admissible blowup 後の有限性と開包含の準コンパクト性。
-/
instance blowup_isNoetherian [_root_.AlgebraicGeometry.IsNoetherian X] :
    _root_.AlgebraicGeometry.IsNoetherian (blowup I) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (blowupπ I)
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (blowupπ I)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
