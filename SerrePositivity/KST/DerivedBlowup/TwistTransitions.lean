module

public import SerrePositivity.KST.DerivedBlowup.ChartCochainCocycle
public import SerrePositivity.KST.DerivedBlowup.ExteriorDGCategory

/-!
概要：KST §3.1 の O(m) のチャート推移単元を Koszul cochain 射に装備する。
方針：Koszul 遷移射に推移単元の整数冪を掛け、単元と基底変換の cocycle を合わせる。
規約：O(1) は S_k の推移単元、O(-1) はその逆。層の降下は別工程。
使われ方：射影空間と導来 blowup 上の捻りの局所データ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {B : Type u} [CommRing B]

/-- 概要：Koszul 複体に単元を掛ける複体自己同型。
方針：逆単元を逆射として使う。
規約：KST §3.1。使われ方：可逆層の基底の変更。 -/
def koszulScalarIso {M : Type u} [AddCommGroup M] [Module B M]
    (d : M →ₗ[B] B) (s : Bˣ) : exteriorKoszulCochain d ≅ exteriorKoszulCochain d where
  hom := (s : B) • 𝟙 _
  inv := ((s⁻¹ : Bˣ) : B) • 𝟙 _
  hom_inv_id := by
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
    rw [s.inv_mul, one_smul]
  inv_hom_id := by
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
    rw [s.mul_inv, one_smul]

/-- 概要：線形圏の可換な合成等式はスカラーを掛けた推移射にも延長できる。
方針：合成の双線形性とスカラー積の等式を使う。
規約：KST §3.1 の捻り推移に適用する一般形。使われ方：捻り cocycle の証明。 -/
theorem scalarTwist_comp {C : Type v} [Category.{w} C] [Preadditive C] [Linear B C]
    {P Q T U : C} (f : P ⟶ Q) (g : Q ⟶ T) (k : P ⟶ U) (h : U ⟶ T)
    (a b c : B) (hab : a * b = c) (hfg : f ≫ g = k ≫ h) :
    (a • f) ≫ (b • g) = k ≫ (c • h) := by
  rw [Linear.smul_comp, Linear.comp_smul, smul_smul, hab, hfg, Linear.comp_smul]

variable {I : Type} [DecidableEq I]

/-- 概要：O(m) の推移単元を掛けたチャート Koszul 遷移射。
方針：単元 s の整数冪で通常の cochain 遷移をスカラー倍する。
規約：KST §3.1、m=1 が O(1)。使われ方：捻りの局所遷移データ。 -/
def chartTwistCochainMap (a x : I → B) (i k : I) (s : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) (m : ℤ) :
    chartExteriorCochain a (normalizeCoordinates x s) k ⟶ chartExteriorCochain a x i :=
  ((s ^ m : Bˣ) : B) • chartExteriorCochainMap a x i k s hi hs

/-- 概要：捻った Koszul チャート遷移は三重重なりで cocycle を満たす。
方針：通常の cochain cocycle と整数冪の積保存を合わせる。
規約：KST §3.1、座標同定の移送を明示する。使われ方：O(m) の降下データ。 -/
theorem chartTwistCochainMap_cocycle (a x : I → B) (i k l : I) (s t : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) (ht : ↑t = normalizeCoordinates x s l) (m : ℤ) :
    chartTwistCochainMap a (normalizeCoordinates x s) k l t
        (normalizeCoordinates_pivot x k s hs) ht m ≫
      chartTwistCochainMap a x i k s hi hs m =
      eqToHom (congrArg exteriorKoszulCochain
        (congrArg (fun y => chartKoszulDifferential a y l) (normalizeCoordinates_cocycle x s t))) ≫
        chartTwistCochainMap a x i l (s * t) hi (transitionUnit_cocycle x l s t ht) m := by
  dsimp only [chartTwistCochainMap]
  apply scalarTwist_comp
  · rw [mul_zpow, Units.val_mul, mul_comm]
  · exact chartExteriorCochainMap_cocycle a x i k l s t hi hs ht

/-- 概要：捻ったチャート遷移は複体同型の Hom 射。
方針：通常のチャート同型に単元の整数冪による自己同型を合成する。
規約：KST §3.1。使われ方：捻りの可逆性。 -/
def chartTwistCochainIso (a x : I → B) (i k : I) (s : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) (m : ℤ) :
    chartExteriorCochain a (normalizeCoordinates x s) k ≅ chartExteriorCochain a x i :=
  chartExteriorCochainIso a x i k s hi hs ≪≫ koszulScalarIso (chartKoszulDifferential a x i) (s ^ m)

/-- 概要：捻りの複体同型の順射は指定した単元冪の遷移射。
方針：単位射のスカラー倍との合成を線形性で整理する。
規約：KST §3.1。使われ方：捻り遷移の可逆性と cocycle の接続。 -/
theorem chartTwistCochainIso_hom (a x : I → B) (i k : I) (s : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) (m : ℤ) :
    (chartTwistCochainIso a x i k s hi hs m).hom = chartTwistCochainMap a x i k s hi hs m := by
  change (chartExteriorCochainIso a x i k s hi hs).hom ≫ (((s ^ m : Bˣ) : B) • 𝟙 _) = _
  rw [Linear.comp_smul, Category.comp_id]
  rfl

end SerrePositivity.KST.DerivedBlowup
