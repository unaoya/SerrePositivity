module
public import SerrePositivity.KST.SConstruction.SerreCubeDegreeLiftRecovery
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorExt

/-! # 元の次数線形射と全 tensor 生成元値の同値
概要：元の各次数からの線形射は、元の全端点・辺 tensor 生成元の任意の値と同値。
方針：元の復元の値の回収と元の生成元判定で両逆律を示す。
規約：元の加群と全生成元を保持。使われ方：実 Hom 逆射の次数ごとの存在と一意性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の次数線形射の全生成元値を復元すると、元の同じ線形射が戻る。 -/
lemma serreCubeDegreeLift_recovery (n : ℕ) (k : ℤ) (V : ModuleCat.{u} A)
    (f : (serreCubeComplex A n).X k ⟶ V) :
    serreCubeDegreeLift A n k V (fun i hi =>
      f (eqToHom (congrArg (fun d => (serreCubeComplex A n).X d) hi)
        (serreCubeGenerator A n i))) = f := by
  apply serreCube_degree_hom_ext A n k
  intro i hi
  exact serreCubeDegreeLift_generator A n k V _ i hi

/-- 元の次数加群からの線形射と、元の全 tensor 生成元の任意の値の実際の同値。 -/
def serreCubeDegreeValuesEquiv (n : ℕ) (k : ℤ) (V : ModuleCat.{u} A) :
    ((serreCubeComplex A n).X k ⟶ V) ≃
      (∀ i : SerreCubeGeneratorIndex n, serreCubeGeneratorDegree n i = k → V) where
  toFun f i hi := f (eqToHom (congrArg (fun d => (serreCubeComplex A n).X d) hi)
    (serreCubeGenerator A n i))
  invFun := serreCubeDegreeLift A n k V
  left_inv := serreCubeDegreeLift_recovery A n k V
  right_inv v := by
    funext i hi
    exact serreCubeDegreeLift_generator A n k V v i hi

/-- 元の生成元値からの線形復元は、元の任意の線形射による後合成と可換。 -/
lemma serreCubeDegreeLift_post (n : ℕ) (k : ℤ) {V W : ModuleCat.{u} A}
    (v : ∀ i : SerreCubeGeneratorIndex n, serreCubeGeneratorDegree n i = k → V)
    (g : V ⟶ W) :
    serreCubeDegreeLift A n k V v ≫ g =
      serreCubeDegreeLift A n k W (fun i hi => g (v i hi)) := by
  apply serreCube_degree_hom_ext A n k
  intro i hi
  exact (congrArg (fun w => g w) (serreCubeDegreeLift_generator A n k V v i hi)).trans
    (serreCubeDegreeLift_generator A n k W (fun j hj => g (v j hj)) i hi).symm

end SerrePositivity.KST.SConstruction
