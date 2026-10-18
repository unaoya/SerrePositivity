module

public import SerrePositivity.KST.Comparison.HomologyAnodyne
public import SerrePositivity.KST.Comparison.GrouplikeComparison

/-!
# Kan 模型と整数ホモロジー

概要：anodyne 局所化の同型を実際の整数ホモロジー同型へ移す。
方針：整数ホモロジーが全ての anodyne map を反転することから局所化に沿って持ち上げる。
規約：Segal 1974 Proposition 1.5、Waldhausen LNM 1126 §1.7・§1.8。
使われ方：Kan 置換、群状モノイドの群完備化、plus の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory
open SerrePositivity.SimplicialModel

/--
概要：anodyne な Kan 置換の単位は整数ホモロジー同型を誘導する。
方針：既存の実際の置換の単位の anodyne 性を使う。
規約：置換の存在やホモロジー比較を仮定しない。
使われ方：セル添付した単体集合を Kan 複体へ移す。
-/
theorem kanReplacementUnit_integralHomologyIsomorphism (X : SSet.{u}) :
    IntegralHomologyIsomorphism (AnodyneKanReplacement.unit.app X) :=
  integralHomologyIsomorphism_of_anodyne _ (AnodyneKanReplacement.unit_anodyne X)

/--
概要：anodyne 局所化で可逆な写像は整数ホモロジー同型を誘導する。
方針：整数ホモロジーを局所化へ持ち上げ、因子分解の自然同型を使う。
規約：実際の正規化整数ホモロジーについての帰結。
使われ方：既存の分類空間の局所化比較との接続。
-/
theorem integralHomologyIsomorphism_of_localized_isIso {X Y : SSet.{u}}
    (f : X ⟶ Y) (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) :
    IntegralHomologyIsomorphism f := by
  intro n
  let H := integralHomologyFunctor.{u} n
  have hH : SSet.anodyneExtensions.IsInvertedBy H :=
    fun _ _ g hg => integralHomologyIsomorphism_of_anodyne g hg n
  let L := Localization.lift H hH AnodyneHomotopy.anodyneQ
  let e : AnodyneHomotopy.anodyneQ ⋙ L ≅ H := Localization.fac H hH _
  have : IsIso (AnodyneHomotopy.anodyneQ.map f) := hf
  have h : H.map f = e.inv.app X ≫ L.map (AnodyneHomotopy.anodyneQ.map f) ≫ e.hom.app Y :=
    (NatIso.naturality_1 e f).symm
  change IsIso (H.map f)
  rw [h]
  infer_instance

/--
概要：群状単体的モノイドの標準群完備化写像は整数ホモロジー同型を誘導する。
方針：証明済みの Segal の標準比較の局所化可逆性を整数ホモロジーへ渡す。
規約：Segal 1974 Proposition 1.5。単体ごとの群性も元のモノイドの Kan 性も要求しない。
使われ方：KST の群状 ĜL の群完備化とホモロジーの接続。
-/
theorem monoidGroupCompletionMap_integralHomologyIsomorphism
    (M : SimplicialObject MonCat.{u}) (hM : SimplicialMonoid.IsGrouplike M) :
    IntegralHomologyIsomorphism (monoidGroupCompletionMap M) :=
  integralHomologyIsomorphism_of_localized_isIso _
    (monoidGroupCompletionMap_localized_isIso M hM)

end SerrePositivity.KST.Comparison
