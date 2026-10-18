module

public import SerrePositivity.KST.Comparison.Homology
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# 正規化された整数ホモロジーのホモトピー不変性

概要：単体的ホモトピーは正規化された整数ホモロジーの同じ射を誘導する。
方針：自由単体的アーベル群の alternating face map complex で鎖ホモトピーを作り、自然な正規化比較で戻す。
規約：Weibel K-book III、Waldhausen LNM 1126 §1.7・§1.8 のホモロジー比較の基礎。
使われ方：plus 構成と Kan 模型のホモロジーの不変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory AlgebraicTopology

/--
概要：恒等射の整数ホモロジーの誘導射は恒等射である。
方針：構成した関手の恒等法則を使う。
規約：全自然数次数。
使われ方：ホモトピー逆からホモロジー逆を構成する。
-/
@[simp] theorem integralHomologyMap_id (X : SSet.{u}) (n : ℕ) :
    integralHomologyMap (𝟙 X) n = 𝟙 (integralHomology X n) :=
  (integralHomologyFunctor n).map_id X

/--
概要：合成の整数ホモロジーの誘導射は誘導射の合成である。
方針：正規化ホモロジー関手の合成法則を使う。
規約：全自然数次数。
使われ方：ホモロジー同型の合成と二対三性。
-/
@[reassoc] theorem integralHomologyMap_comp {X Y Z : SSet.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    integralHomologyMap (f ≫ g) n = integralHomologyMap f n ≫ integralHomologyMap g n :=
  (integralHomologyFunctor n).map_comp f g

/--
概要：単体的ホモトピーは非正規化された整数鎖複体の鎖ホモトピーを与える。
方針：組合せ的な単体的ホモトピーを自由関手で移し、交互面複体の鎖ホモトピーを作る。
規約：任意の二つの単体写像。
使われ方：正規化ホモロジーのホモトピー不変性。
-/
def unnormalizedIntegralChainsHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) :
    Homotopy (unnormalizedIntegralChains.map f) (unnormalizedIntegralChains.map g) :=
  (H.toSimplicialObjectHomotopy.whiskerRight AddCommGrpCat.free).toChainHomotopy

/--
概要：ホモトピックな単体写像は同じ整数ホモロジーの射を誘導する。
方針：非正規化側の鎖ホモトピーの写像の一致を、正規化比較の自然性で戻す。
規約：実際の正規化複体のホモロジーに対して述べる。
使われ方：plus の構成の選択や Kan 模型の比較。
-/
theorem integralHomologyMap_eq_of_homotopy {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (n : ℕ) : integralHomologyMap f n = integralHomologyMap g n := by
  have h : (unnormalizedIntegralHomologyFunctor n).map f =
      (unnormalizedIntegralHomologyFunctor n).map g :=
    (unnormalizedIntegralChainsHomotopy H).homologyMap_eq n
  apply (cancel_mono ((normalizationHomologyNatIso n).hom.app Y)).mp
  rw [(normalizationHomologyNatIso n).hom.naturality f,
    (normalizationHomologyNatIso n).hom.naturality g, h]

/--
概要：単体写像が全次数の整数ホモロジー同型を誘導する条件。
方針：構成した整数ホモロジーの射の可逆性で定義する。
規約：局所係数を含む acyclic 性とは区別する。
使われ方：plus の整数係数での帰結。
-/
def IntegralHomologyIsomorphism {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  ∀ n : ℕ, IsIso (integralHomologyMap f n)

/--
概要：実際の単体的ホモトピー逆は整数ホモロジーの同型を誘導する。
方針：逆写像の誘導射を逆とし、両合成のホモトピー不変性を使う。
規約：比較や同値の存在を追加公理として仮定しない。
使われ方：構成した収縮と標準単体のホモロジー比較。
-/
def integralHomologyIsoOfHomotopyInverse {X Y : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : SSet.Homotopy (f ≫ g) (𝟙 X)) (hgf : SSet.Homotopy (g ≫ f) (𝟙 Y)) (n : ℕ) :
    integralHomology X n ≅ integralHomology Y n where
  hom := integralHomologyMap f n
  inv := integralHomologyMap g n
  hom_inv_id := by
    rw [← integralHomologyMap_comp, integralHomologyMap_eq_of_homotopy hfg, integralHomologyMap_id]
  inv_hom_id := by
    rw [← integralHomologyMap_comp, integralHomologyMap_eq_of_homotopy hgf, integralHomologyMap_id]

end SerrePositivity.KST.Comparison
