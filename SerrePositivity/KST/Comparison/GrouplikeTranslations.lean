module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Comparison.MonoidTranslations
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# 群状性と平行移動の局所化可逆性

概要：群状単体的モノイドの平行移動は anodyne 局所化で同型となる。
方針：実ホモトピーの局所化不変性と逆成分の平行移動を使う。
規約：Segal 1974 Proposition 1.5・1.6。全単体次数の逆元を要求しない。
使われ方：bar の面写像のホモトピーファイバー比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：群状モノイドの左平行移動は anodyne 局所化で可逆である。
方針：ホモトピー不変性を局所化関手について供給し、逆成分の射で逆を作る。
規約：Segal 1974 Proposition 1.5・1.6 の作用の仮定を満たす部分。
使われ方：正則 bar のホモトピーファイバー比較。
-/
theorem grouplikeTranslation_localized_isIso (M : SimplicialObject MonCat.{u})
    (hG : SimplicialMonoid.IsGrouplike M) (a : M.obj (op ⦋0⦌)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (monoidLeftTranslation M a)) :=
  (grouplikeTranslationIso M hG AnodyneHomotopy.anodyneQ
    (AnodyneHomotopy.map_homotopy_eq _
      (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)) a).isIso_hom

end SerrePositivity.KST.Comparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "5.2.6.4" (partial := component) "仮定：厳密単体的モノイド M の π₀ の全成分が単元（Lean が強い：厳密模型と π₀ による条件を指定）。結論：π₀ に誘導乗法を保つ群構造が付き、各頂点の左平行移動は anodyne 局所化で可逆となる（原典の π₀ の群性と左平行移動の同値という部分に一致）。全 E₁ 空間の shear 判定の両方向と右側は含まれない。"] _root_.SerrePositivity.KST.Comparison.grouplikeTranslation_localized_isIso
