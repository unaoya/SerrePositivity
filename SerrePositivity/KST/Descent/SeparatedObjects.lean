module

public import SerrePositivity.KST.Descent.ClosedCoverPullback
public import SerrePositivity.KST.Descent.FiniteTypeReduction

/-!
# 帰納で使う有限型対象の分離性

## 概要
閉部分への引き戻し・交わり・被約化で、始域の基底 S 上の分離性を保持する。

## 方針
構造射を閉埋め込みと元の分離な構造射の合成として検査する。

## 規約
スキームが絶対的に分離であることは仮定せず、S 上の分離性を使う。

## 使われ方
論文 補題 3.3・定理 3.1 の閉和と次元帰納の局所射への仮定の移行。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：閉中心への引き戻しの始域は S 上分離（論文 補題 3.3）。
方針：閉埋め込みである第一射影と元の構造射を合成する。
規約：引き戻しの被約性は不要。
使われ方：閉部分上の局所降下への帰納仮定の適用。 -/
theorem closedImmersionPullback_isSeparated {S : Scheme.{u}}
    {B V Z : FiniteTypeSchemes S} (f : V ⟶ B) (i : Z ⟶ B)
    [IsClosedImmersion i.hom.left] [IsSeparated V.obj.hom] :
    IsSeparated (closedImmersionPullback f i).obj.hom :=
  inferInstanceAs (IsSeparated (pullback.fst f.hom.left i.hom.left ≫ V.obj.hom))

/-- 概要：閉被覆の引き戻しの実際の交わりも S 上分離（論文 補題 3.3）。
方針：第一の閉部分への分離性をさらに引き戻す。
規約：二重の引き戻しの指定対象を保持する。
使われ方：低次元の交わりへの帰納仮定の適用。 -/
theorem closedCoverPullbackIntersection_isSeparated {S : Scheme.{u}}
    {B V Y Z : FiniteTypeSchemes S} (f : V ⟶ B) (i : Y ⟶ B) (j : Z ⟶ B)
    [IsClosedImmersion i.hom.left] [IsClosedImmersion j.hom.left] [IsSeparated V.obj.hom] :
    IsSeparated (closedCoverPullbackSquare f i j).X₁.obj.hom :=
  @closedImmersionPullback_isSeparated S V (closedImmersionPullback f i)
    (closedImmersionPullback f j) (closedImmersionSquare f i).f₁₂ (closedImmersionSquare f j).f₁₂
    (closedImmersionSquare_first_isClosedImmersion f j) (closedImmersionPullback_isSeparated f i)

/-- 概要：有限型対象の被約化は S 上の分離性を保つ（論文 定理 3.1）。
方針：被約化の閉包含と元の構造射を合成する。
規約：Noether 性は不要。
使われ方：一般の始域を被約化する帰納の移行。 -/
theorem finiteTypeReduction_isSeparated {S : Scheme.{u}} (X : FiniteTypeSchemes S)
    [IsSeparated X.obj.hom] : IsSeparated (finiteTypeReduction X).obj.hom :=
  inferInstanceAs (IsSeparated (schemeReductionInclusion X.obj.left ≫ X.obj.hom))

end SerrePositivity.KST.Descent
