module

public import SerrePositivity.KST.DerivedGeometry.OpenImmersionTensorSheaf
public import SerrePositivity.KST.DerivedGeometry.CoefficientRegularMap

/-!
# 開埋め込みに沿う正則構造層加群の比較

概要：具体的係数環層の正則 O 加群の形成を任意の開埋め込みに沿う制限と比較する。
方針：構造層射を保つ環層同型を正則加群へ送り、切断上の恒等比較と合成する。
規約：スキーム同型にも適用できる。
使われ方：KST D4・T1、Toën Derived Azumaya §3.2 の準連接性の輸送。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry

namespace CoefficientSheaf

variable {X Y : Scheme.{u}} (B : CoefficientSheaf Y) (f : X ⟶ Y) [IsOpenImmersion f]

/--
概要：正則 O 加群の開埋め込みへの制限と係数環層の制限の正則加群を比較する。
方針：同じ開像の切断上の恒等写像に O 線形性を添える。
規約：双方の作用は appIso の逆を用いる。
使われ方：KST D4、Toën §3.2 の正則加群の輸送。
-/
def regularRestrictAlongMap :
    (Scheme.Modules.restrictFunctor f).obj B.regular ⟶ (B.restrictAlong f).regular where
  val := PresheafOfModules.homMk (𝟙 _) (fun _ _ _ => rfl)

/--
概要：正則加群と任意の開埋め込みの制限の比較射は同型。
方針：基礎加法群の層への忘却で恒等射になることを使う。
規約：構造層上の線形性は比較射の構成で保証する。
使われ方：KST D4、Toën §3.2 の準連接性の輸送。
-/
instance regularRestrictAlongMap_isIso : IsIso (regularRestrictAlongMap B f) := by
  let := PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
    (R := X.ringCatSheaf)
  have : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map
      (regularRestrictAlongMap B f)) := by
    change IsIso (𝟙 _)
    infer_instance
  exact isIso_of_reflects_iso (regularRestrictAlongMap B f) (SheafOfModules.toSheaf X.ringCatSheaf)

/--
概要：正則加群の形成と任意の開埋め込みへの制限は標準的に可換。
方針：構成した恒等切断上の比較射を同型として束ねる。
規約：Mathlib の構造層加群の制限関手との比較。
使われ方：KST D4、Toën §3.2 の局所模型の輸送。
-/
def regularRestrictAlongIso :
    (Scheme.Modules.restrictFunctor f).obj B.regular ≅ (B.restrictAlong f).regular :=
  asIso (regularRestrictAlongMap B f)

end CoefficientSheaf

variable {A : Type u} [CommRing A] (H : Type u) [Ring H] [Algebra A H]
  {X Y : Scheme.{u}} (a : A →+* Γ(Y, ⊤)) (f : X ⟶ Y) [IsOpenImmersion f]

/--
概要：具体的係数環層の正則 O 加群は開埋め込みに沿う制限と可換。
方針：環層の同型を正則加群へ送り、正則加群の制限同型を合成する。
規約：始域の基礎環作用は大域切断の引き戻しで指定する。
使われ方：KST D4・T1、Toën §3.2 のアフィン同型に沿う準連接性の輸送。
-/
def openImmersionTensorRegularIso :
    (tensorCoefficientSheaf H (pullbackBaseMap a f)).regular ≅
      (Scheme.Modules.restrictFunctor f).obj (tensorCoefficientSheaf H a).regular :=
  asIso (CoefficientSheaf.regularMap (openImmersionTensorSheafIso H a f).hom
    (openImmersionTensorSheafIso_structureMap H a f)) ≪≫
  (CoefficientSheaf.regularRestrictAlongIso (tensorCoefficientSheaf H a) f).symm

/--
概要：具体的係数環層の正則 O 加群の準連接性は開埋め込みへの制限で保たれる。
方針：Mathlib の制限関手の準連接性保存と構成した正則加群の同型を使う。
規約：終域での準連接性を仮定として明示する。
使われ方：KST D4・T1、Toën §3.2 のアフィン同型への輸送。
-/
theorem tensorRegular_isQuasicoherent_pullback
    [(tensorCoefficientSheaf H a).regular.IsQuasicoherent] :
    (tensorCoefficientSheaf H (pullbackBaseMap a f)).regular.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (openImmersionTensorRegularIso H a f).symm inferInstance

end SerrePositivity.KST.DerivedGeometry
