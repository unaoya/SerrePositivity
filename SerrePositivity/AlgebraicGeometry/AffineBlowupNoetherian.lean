module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.BlowupChartIdeals

/-!
概要：KST §5、Stacks 0815 の Noether アフィン基底の通常 blowup の Noether 性。
方針：有限生成中心の固有性から局所 Noether 性とコンパクト性を得る。
規約：中心は Noether 条件から有限生成となる。
使われ方：最初の分子中心の blowup 上で局所中心を延長し共通細分する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry

/--
概要：Noether 環の通常のアフィン blowup は Noether スキーム。
方針：構造射の固有性から有限型性と準コンパクト性を使う。
規約：KST §5、Stacks 0815、任意のイデアル中心を扱う。
使われ方：チャートごとの局所平坦化中心の大域化。
-/
instance affineBlowup_isNoetherian {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : _root_.AlgebraicGeometry.IsNoetherian (affineBlowup I) := by
  have : IsProper (affineBlowupπ I) := affineBlowupπ_isProper I (Ideal.fg_of_isNoetherianRing I)
  exact {
    toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (affineBlowupπ I)
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (affineBlowupπ I) }

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
