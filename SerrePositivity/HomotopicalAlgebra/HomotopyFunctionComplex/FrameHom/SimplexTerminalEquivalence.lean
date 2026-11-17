module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalStandard
public import SerrePositivity.HomotopicalAlgebra.Simplicial.CellularNaturalComparison

/-!
# 任意の単体集合での終端 augmentation の反転性

概要：反対要素圏の元の終端 augmentation は全単体集合で anodyne 反転後に可逆。
方針：元の標準単体の収縮から境界の貼り合わせと実際の骨格余極限で拡張する。
規約：標準単体だけの結論ではなく任意の単体集合を扱い、単体集合モデルは要求しない。
使われ方：Dwyer–Kan §7 の共通比較の frame 側の反転可能な左射。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v uH vH

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve

open _root_.CategoryTheory
open _root_.SerrePositivity.SimplicialModel

/-- 概要：同じ終端 augmentation は任意の単体集合で anodyne 反転後に可逆（Dwyer–Kan §7）。
方針：元の関手の余連続性・単射保存と標準単体の反転性から cellular に帰納する。
規約：元の比較射・境界・骨格余極限を保持する。
使われ方：実際の Map^h の反対要素圏との共通比較。 -/
lemma augmentation_localized_isIso (K : SSet.{v}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation.app K)) :=
  CellularNaturalComparison.app_isIso _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation
    (fun n => _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.standardAugmentation_isIso AnodyneHomotopy.anodyneQ
      (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions) n) K

variable {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
/-- 概要：同じ終端 augmentation は任意の anodyne 反転関手で同型（Dwyer–Kan §7）。
方針：元の anodyne 局所化の反転性を普遍性で移す。
規約：局所化の余連続性や単体集合モデルは要求しない。
使われ方：元の Map^h を保った高次比較の左射。 -/
lemma augmentation_image_isIso (K : SSet.{v}) : IsIso (L.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation.app K)) :=
  AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL _ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation_localized_isIso K)

include hL in
/-- 概要：同じ終端 augmentation は全単体集合に自然な局所化後の同型（Dwyer–Kan §7）。
方針：元の比較射の全係数自然性と各成分の反転性を束ねる。
規約：同型の順射は元の augmentation の像そのもの。
使われ方：共通比較の frame 側の関手的な同定。 -/
def augmentationImageIso : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.functor.{v} ⋙ L ≅ L :=
  NatIso.ofComponents (fun K => by
    have : IsIso (L.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation.app K)) := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation_image_isIso L hL K
    exact asIso (L.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation.app K))) (by
      intro K M f
      change L.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.functor.map f) ≫ L.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation.app M) =
        L.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation.app K) ≫ L.map f
      rw [← L.map_comp, ← L.map_comp, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.augmentation.naturality]
      rfl)

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve
