module
public import SerrePositivity.KST.ProExcision.MonoidReverseOpposite

/-!
# 係数の単体方向を保つ反対モノイド関手

概要：各次数の乗法だけを反転する実関手を構成する。
方針：反対準同型を用い、係数方向の rev とは独立に扱う。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：右作用の行側半直積の実模型。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory

/-- 概要：モノイドとその実準同型の反対モノイド関手。
方針：台の反対型と反対準同型を使う。
規約：SW92 §1.2。使われ方：行側の右作用を左作用として表す。 -/
def monCatOpposite : MonCat.{u} ⥤ MonCat.{u} where
  obj M := MonCat.of Mᵐᵒᵖ
  map f := MonCat.ofHom (MonoidHom.op f.hom)

/-- 概要：乗法方向だけを反転した実単体的モノイド。
方針：反対モノイド関手を後合成する。
規約：係数方向を反転しない。SW92 §1.2。
使われ方：実行側半直積の基底と全空間。 -/
def monoidOpposite (M : SimplicialObject MonCat.{u}) : SimplicialObject MonCat.{u} :=
  M ⋙ monCatOpposite

end SerrePositivity.KST.ProExcision
