module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import SerrePositivity.CommutativeAlgebra.Koszul.Basic

/-! # 元の冪のKoszul複体の逆系

指定した元の各冪のKoszul複体と、冪を一段下げる実際の鎖写像を構成する。
その直積とmapping coneから完備化の候補複体を作る。
導来完備性はTowerCompleteで証明する。H⁰の環構造・普遍性はまだ別途証明が必要である。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 各座標を指定した倍数へ変えるKoszul複体の写像。 -/
def koszulComplexMapOfMul : {e : ℕ} → (a b c : Fin e → R) →
    (∀ i, a i = b i * c i) → (koszulComplex a ⟶ koszulComplex b)
  | 0, _, _, _, _ => 𝟙 _
  | e + 1, a, b, c, h =>
    let g := koszulComplexMapOfMul (Fin.init a) (Fin.init b) (Fin.init c)
      (fun i ↦ h i.castSucc)
    HomologicalComplex.homotopyCofiber.mapArrowHom
      (smulId (a (Fin.last e)) (koszulComplex (Fin.init a)))
      (smulId (b (Fin.last e)) (koszulComplex (Fin.init b))) (fun j ↦ ⟨j - 1, by simp⟩)
      (Arrow.homMk (c (Fin.last e) • g) g (by
        change (c (Fin.last e) • g) ≫ (b (Fin.last e) • 𝟙 _) =
          (a (Fin.last e) • 𝟙 _) ≫ g
        simp only [Linear.comp_smul, Linear.smul_comp, id_comp, comp_id, smul_smul, h]))

/-- 指定した元の列の各冪を取ったKoszul複体の逆系。 -/
def powerKoszulTower {e : ℕ} (a : Fin e → R) (n : ℕ) :
    CochainComplex (ModuleCat.{u} R) ℤ := koszulComplex (fun i ↦ a i ^ n)

/-- 冪を一段下げるKoszul複体の鎖写像。 -/
def powerKoszulTransition {e : ℕ} (a : Fin e → R) (n : ℕ) :
    powerKoszulTower R a (n + 1) ⟶ powerKoszulTower R a n :=
  koszulComplexMapOfMul R (fun i ↦ a i ^ (n + 1)) (fun i ↦ a i ^ n) a
    (fun i ↦ pow_succ (a i) n)

/-- 冪のKoszul複体のホモトピー逆極限による完備化の候補モデル。 -/
def koszulCompletionComplex {e : ℕ} (a : Fin e → R) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  complexTowerHomotopyLimit R (powerKoszulTower R a) (powerKoszulTransition R a)

/-- 上の候補モデルを標準導来圏へ移した対象。 -/
def koszulCompletionObject {e : ℕ} (a : Fin e → R) : ConcreteDerivedCategory R :=
  DerivedCategory.Q.obj (koszulCompletionComplex R a)

end SerrePositivity.DerivedCompletion
