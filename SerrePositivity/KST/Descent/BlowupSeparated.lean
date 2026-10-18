module

public import SerrePositivity.KST.Descent.BlowupGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# 抽象 blowup の頂点の分離性

## 概要
基底の分離性から blowup 側・閉中心・例外部分の分離性を導く。

## 方針
固有射と閉埋め込みの分離性、および Cartesian な閉埋め込みの底変換を合成する。

## 規約
非アフィンな頂点にアフィン性を仮定しない。基底 S 自体の分離性も不要である。

## 使われ方
論文 補題 3.3 と定理 3.1 の一般の基底変更への切断つき全次数降下。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent.AbstractBlowupSquare

variable {S : Scheme.{u}} (Q : AbstractBlowupSquare S) [IsSeparated Q.square.X₄.obj.hom]

/-- 概要：抽象 blowup の固有射側の頂点は S 上分離（補題 3.3）。
方針：固有射の分離性を基底の構造射と合成する。
規約：アフィン性を使わない。使われ方：非アフィンな blowup 上への降下。 -/
theorem modification_isSeparated : IsSeparated Q.square.X₂.obj.hom := by
  have : IsProper Q.square.f₂₄.hom.left := Q.proper
  have h : IsSeparated (Q.square.f₂₄.hom.left ≫ Q.square.X₄.obj.hom) := inferInstance
  exact Q.square.f₂₄.hom.w ▸ h

/-- 概要：閉中心は S 上分離（補題 3.3）。
方針：閉埋め込みと基底の構造射の分離性を合成する。
規約：中心を被約化しない。使われ方：厚みを保持した閉中心上への降下。 -/
theorem center_isSeparated : IsSeparated Q.square.X₃.obj.hom := by
  have : IsClosedImmersion Q.square.f₃₄.hom.left := Q.closed
  have h : IsSeparated (Q.square.f₃₄.hom.left ≫ Q.square.X₄.obj.hom) := inferInstance
  exact Q.square.f₃₄.hom.w ▸ h

/-- 概要：例外部分は S 上分離（補題 3.3）。
方針：中心の閉埋め込みを Cartesian 正方形で底変換し、固有射側の構造射と合成する。
規約：実際の例外部分と指定された四辺を使う。
使われ方：抽象 blowup の四頂点全てでの切断つき降下。 -/
theorem exceptional_isSeparated : IsSeparated Q.square.X₁.obj.hom := by
  have : IsClosedImmersion Q.square.f₁₂.hom.left :=
    MorphismProperty.of_isPullback Q.cartesian.flip Q.closed
  have : IsSeparated Q.square.X₂.obj.hom := Q.modification_isSeparated
  have h : IsSeparated (Q.square.f₁₂.hom.left ≫ Q.square.X₂.obj.hom) := inferInstance
  exact Q.square.f₁₂.hom.w ▸ h

end SerrePositivity.KST.Descent.AbstractBlowupSquare
