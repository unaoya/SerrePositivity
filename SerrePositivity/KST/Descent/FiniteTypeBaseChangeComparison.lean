module

public import SerrePositivity.KST.Descent.FiniteTypeBaseChangeFunctor

/-!
# 指定モデルと圏の選択された底変換との自然な比較

## 概要
実際の finiteTypePullback の底変換関手と、圏の選択された pullback の底変換関手を自然同型で結ぶ。

## 方針
各基底上の対象で Cartesian 正方形の標準同型を使い、射に関する自然性を二射影で検査する。

## 規約
対象の型クラスを変更しない。比較の hom は第一・第二射影を同時に保つ。

## 使われ方
論文 補題 3.2・3.3 の抽象 blowup の指定底変換と混合 Čech の選択された底変換の接続。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FiniteTypeSchemes S} (f : X ⟶ Y)

/-- 概要：指定モデルと選択された引き戻しとの標準同型（補題 3.3）。
方針：指定モデルの実際の Cartesian 性を使う。
規約：同じ基底上の対象と射。使われ方：元の Čech 関手の選択との比較。 -/
noncomputable def finiteTypeBaseChangeIso (Z : Over Y) :
    finiteTypePullback f Z.hom ≅ pullback f Z.hom :=
  (finiteTypePullback_isPullback f Z.hom).isoPullback

/-- 概要：モデルの標準同型は第一射影を保つ（補題 3.3）。方針：Cartesian 標準同型の公式。
規約：指定第一射影そのもの。使われ方：元の射への自然比較との整合性。 -/
@[reassoc (attr := simp)] theorem finiteTypeBaseChangeIso_hom_fst (Z : Over Y) :
    (finiteTypeBaseChangeIso f Z).hom ≫ pullback.fst f Z.hom = finiteTypePullbackFst f Z.hom :=
  (finiteTypePullback_isPullback f Z.hom).isoPullback_hom_fst

/-- 概要：モデルの標準同型は第二射影を保つ（補題 3.3）。方針：Cartesian 標準同型の公式。
規約：指定第二射影そのもの。使われ方：同じ基底上の Arrow 比較。 -/
@[reassoc (attr := simp)] theorem finiteTypeBaseChangeIso_hom_snd (Z : Over Y) :
    (finiteTypeBaseChangeIso f Z).hom ≫ pullback.snd f Z.hom = finiteTypePullbackSnd f Z.hom :=
  (finiteTypePullback_isPullback f Z.hom).isoPullback_hom_snd

/-- 概要：指定モデルと選択された引き戻しの比較を Arrow の同型にする（補題 3.3）。
方針：基底側を恒等同型とし、第二射影を保つ標準同型を使う。
規約：構造射を保持する同型。使われ方：Čech nerve 関手による図式全体の比較。 -/
noncomputable def finiteTypeBaseChangeArrowIso (Z : Over Y) :
    (finiteTypeOverBaseChangeArrow f).obj Z ≅ (overBaseChangeArrow f).obj Z :=
  Arrow.isoMk (finiteTypeBaseChangeIso f Z) (Iso.refl Z.left)
    ((finiteTypeBaseChangeIso_hom_snd f Z).trans (Category.comp_id _).symm)

set_option backward.isDefEq.respectTransparency false in
/-- 概要：指定モデルと選択された底変換の Arrow 関手は自然同型（補題 3.3）。
方針：各基底上の標準同型の自然性を選択された引き戻しの二射影で検査する。
規約：Over の全射について成立し、各 Čech 段で別の同型を選び直さない。
使われ方：実際の抽象 blowup 底変換と混合二重 Čech の全単体射を同じ比較で接続する。 -/
noncomputable def finiteTypeBaseChangeArrowNatIso :
    finiteTypeOverBaseChangeArrow f ≅ overBaseChangeArrow f :=
  NatIso.ofComponents (finiteTypeBaseChangeArrowIso f) (fun {Z Z'} α ↦ by
    apply Arrow.hom_ext
    · change finiteTypeBaseChangeMap f α ≫ (finiteTypeBaseChangeIso f Z').hom =
        (finiteTypeBaseChangeIso f Z).hom ≫ ((overBaseChangeArrow f).map α).left
      apply pullback.hom_ext <;> simp [Category.assoc, overBaseChangeArrow, pullback.map]
    · change α.left ≫ 𝟙 Z'.left = (𝟙 Z.left) ≫ α.left
      simp)

end SerrePositivity.KST.Descent
