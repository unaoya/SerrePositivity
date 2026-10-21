module
public import SerrePositivity.KST.SConstruction.SerreIntervalDegreeLift
public import SerrePositivity.KST.SConstruction.SerreCubeGenerators

/-! # 元の全 tensor 生成元の値からの次数線形復元
概要：元の全端点・辺 tensor 生成元の指定次数の任意の値から、元の次数線形射を作る。
方針：元の区間の線形復元を curry し、元の tensor の双次数直和へ降ろして帰納する。
規約：元の加群・非有界 total tensor を保持。使われ方：native HA からの実 Hom 逆射。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の指定次数の全 tensor 生成元の任意の値を、元の次数加群の線形射へ延長する。 -/
def serreCubeDegreeLift : (n : ℕ) → (k : ℤ) → (V : ModuleCat.{u} A) →
    (∀ i : SerreCubeGeneratorIndex n, serreCubeGeneratorDegree n i = k → V) →
    ((serreCubeComplex A n).X k ⟶ V)
  | 0, k, V, v => if hk : k = 0 then
      eqToHom (congrArg (fun d => (serreCubeComplex A 0).X d) hk) ≫
        (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom ≫
          moduleElementMap A V (v PUnit.unit hk.symm)
    else 0
  | n + 1, _k, V, v => HomologicalComplex₂.totalDesc _ (fun p q hpq =>
      ModuleCat.ofHom (TensorProduct.lift
        (serreCubeDegreeLift n p (ModuleCat.of A ((serreInterval A).X q →ₗ[A] V))
          (fun i hi => (serreIntervalDegreeLift A q V (fun j hj =>
            v (i, j) ((congrArg₂ (fun x y : ℤ => x + y) hi hj).trans hpq))).hom)).hom))

/-- 元の復元射を双次数包含へ制限すると、同じ元の curry した両生成元復元を回収する。 -/
lemma serreCubeDegreeLift_succ_ι (n : ℕ) (k : ℤ) (V : ModuleCat.{u} A)
    (v : ∀ i : SerreCubeGeneratorIndex (n + 1), serreCubeGeneratorDegree (n + 1) i = k → V)
    (p q : ℤ) (hpq : p + q = k) :
    ιTensorObj (serreCubeComplex A n) (serreInterval A) p q k hpq ≫
      serreCubeDegreeLift A (n + 1) k V v =
    ModuleCat.ofHom (TensorProduct.lift
      (serreCubeDegreeLift A n p (ModuleCat.of A ((serreInterval A).X q →ₗ[A] V))
        (fun i hi => (serreIntervalDegreeLift A q V (fun j hj =>
          v (i, j) ((congrArg₂ (fun x y : ℤ => x + y) hi hj).trans hpq))).hom)).hom) := by
  dsimp only [serreCubeDegreeLift]
  exact HomologicalComplex₂.ι_totalDesc _ _ p q hpq

end SerrePositivity.KST.SConstruction
