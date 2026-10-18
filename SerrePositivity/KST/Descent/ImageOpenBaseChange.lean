module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# スキーム論的像と開埋め込みによる底変換

## 概要
準コンパクトな射の実際のスキーム論的像は、開埋め込みによる底変換と両立する。

## 方針
開部分上の核イデアル層の公式を比較し、同じ核を持つ閉埋め込みの lift で同型を構成する。

## 規約
像は構造層を持つスキーム論的像であり、点集合の閉包の主張ではない。

## 使われ方
論文 補題 3.3、公理 (6) の global strict transform とアフィンチャートの比較。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
  [QuasiCompact f] [IsOpenImmersion g]

/-- 概要：開埋め込みの実際の Cartesian 正方形で核が引き戻しと両立（論文 補題 3.3）。
方針：任意のアフィン開集合で核の公式とイデアル層の引き戻しの公式を比較する。
規約：選択された引き戻し対象と異なる具体的なアフィンモデルにも適用できる。
使われ方：strict transform のアフィンチャートの核イデアル層の同定。 -/
theorem ker_of_openBaseChange {P : Scheme.{u}} (p : P ⟶ Z) (q : P ⟶ X)
    (h : IsPullback p q g f) : p.ker = f.ker.comap g := by
  apply Scheme.IdealSheafData.ext
  funext W
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f p q g h W).trans
    (Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion f.ker g W).symm

/-- 概要：開埋め込みによる底変換後の核は元の核の引き戻し（論文 補題 3.3）。
方針：全アフィン開集合で核とイデアル層の引き戻しの同じ公式を比較する。
規約：準コンパクト性を明示し、一般の像の底変換を無条件には主張しない。
使われ方：strict transform の開チャートにおけるスキーム論的像。 -/
theorem ker_pullback_open :
    (pullback.snd f g).ker = f.ker.comap g := by
  exact ker_of_openBaseChange f g (pullback.snd f g) (pullback.fst f g)
    (IsPullback.of_hasPullback f g).flip

/-- 概要：元の像の引き戻しの閉包含と局所の像の閉包含は同じ核を持つ（論文 補題 3.3）。
方針：閉埋め込みの引き戻しの核と、開底変換後の核の公式を合成する。
規約：選択された実際の引き戻しを使う。
使われ方：二つの閉スキームの間の標準同型。 -/
theorem imageOpenBaseChange_fst_ker :
    (pullback.fst g f.imageι).ker = (pullback.snd f g).imageι.ker := by
  exact (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion f.imageι g).trans
    ((congrArg (fun I : Y.IdealSheafData ↦ I.comap g)
      (Scheme.IdealSheafData.ker_subschemeι f.ker)).trans
        ((ker_pullback_open f g).symm.trans
          (Scheme.IdealSheafData.ker_subschemeι (pullback.snd f g).ker).symm))

/-- 概要：開底変換の任意の具体的モデルの像と元の像の引き戻しの同型（論文 補題 3.3）。
方針：Cartesian 正方形の核の公式から同じ核を持つ閉包含を構成し、その lift を使う。
規約：実際の Cartesian 正方形を要求し、点集合の正方形には弱めない。
使われ方：テンソル積の Spec による strict transform の具体的なチャート比較。 -/
noncomputable def imageOpenBaseChangeIsoOfIsPullback {P : Scheme.{u}}
    (p : P ⟶ Z) (q : P ⟶ X) (h : IsPullback p q g f) :
    p.image ≅ pullback g f.imageι := by
  have hk : (pullback.fst g f.imageι).ker = p.imageι.ker :=
    (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion f.imageι g).trans
      ((congrArg (fun I : Y.IdealSheafData ↦ I.comap g)
        (Scheme.IdealSheafData.ker_subschemeι f.ker)).trans
          ((ker_of_openBaseChange f g p q h).symm.trans
            (Scheme.IdealSheafData.ker_subschemeι p.ker).symm))
  have := IsClosedImmersion.isIso_lift (pullback.fst g f.imageι) p.imageι hk
  exact asIso (IsClosedImmersion.lift (pullback.fst g f.imageι) p.imageι hk.le)

/-- 概要：具体的な開底変換モデルの像の同型は閉包含を保つ（論文 補題 3.3）。
方針：同型の hom が閉埋め込みの指定 lift であることを使う。
規約：開基底への実際の構造射の等式。
使われ方：チャート上の平坦性を global な構造射へ移す。 -/
theorem imageOpenBaseChangeIsoOfIsPullback_hom_fst {P : Scheme.{u}}
    (p : P ⟶ Z) (q : P ⟶ X) (h : IsPullback p q g f) :
    (imageOpenBaseChangeIsoOfIsPullback f g p q h).hom ≫ pullback.fst g f.imageι = p.imageι :=
  IsClosedImmersion.lift_fac _ _ _

/-- 概要：スキーム論的像は開埋め込みによる実際の底変換と同型（論文 補題 3.3）。
方針：同じ核イデアル層を持つ閉包含の lift を同型と判定する。
規約：同型は開基底 Z への閉包含を保つ。
使われ方：global strict transform の開チャートを局所の像と同定する。 -/
noncomputable def imageOpenBaseChangeIso :
    (pullback.snd f g).image ≅ pullback g f.imageι := by
  exact imageOpenBaseChangeIsoOfIsPullback f g (pullback.snd f g) (pullback.fst f g)
    (IsPullback.of_hasPullback f g).flip

/-- 概要：像の開底変換の標準同型は指定された閉包含を保つ（論文 補題 3.3）。
方針：閉埋め込みの lift の実際の因子化式を使う。
規約：選択した射影は開基底 Z への第一射影。
使われ方：strict transform のチャートの構造射との一致。 -/
theorem imageOpenBaseChangeIso_hom_fst :
    (imageOpenBaseChangeIso f g).hom ≫ pullback.fst g f.imageι =
      (pullback.snd f g).imageι :=
  IsClosedImmersion.lift_fac _ _ _

end SerrePositivity.KST.Descent
