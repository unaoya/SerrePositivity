module
public import SerrePositivity.KST.SConstruction.SerreCubeTensorGeneratorExt

/-! # 元の内部端点面の左右生成元対への実作用
概要：内部端点面の全生成元対の像を、左への端点追加と右の同じ添字の連結で回収。
方針：元の実面の tensor 合成元への作用と、端点生成元の次数移送を合わせる。
規約：元の全因子と指定次数を保持。使われ方：HA 一面制限の実 source 評価。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の内部端点面の全生成元対の像は、同じ左端点追加・右添字連結生成元。 -/
lemma serreCubeRightFace_tensor_generator (b : Bool) (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (m : ℕ) (j : SerreCubeGeneratorIndex m) (k : ℤ)
    (hk : serreCubeGeneratorDegree n i + serreCubeGeneratorDegree m j = k) :
    (serreCubeRightFace A b n m).hom.f k
      (serreCubeTensorPair A n m (serreCubeGeneratorDegree n i) (serreCubeGeneratorDegree m j)
        k hk (serreCubeGenerator A n i) (serreCubeGenerator A m j)) =
      eqToHom (congrArg (fun d => (serreCubeComplex A (n + 1 + m)).X d)
        ((serreCubeGeneratorConcat_degree (n + 1) (i, serreCubeGeneratorEndpointIndex b) m j).trans
          ((congrArg (· + serreCubeGeneratorDegree m j)
            (show serreCubeGeneratorDegree (n + 1) (i, serreCubeGeneratorEndpointIndex b) =
              serreCubeGeneratorDegree n i by cases b <;> exact add_zero _)).trans hk)))
        (serreCubeGenerator A (n + 1 + m)
          (serreCubeGeneratorConcat (n + 1) (i, serreCubeGeneratorEndpointIndex b) m j)) := by
  have hd : serreCubeGeneratorDegree (n + 1) (i, serreCubeGeneratorEndpointIndex b) =
      serreCubeGeneratorDegree n i := by cases b <;> exact add_zero _
  have hsum : serreCubeGeneratorDegree (n + 1) (i, serreCubeGeneratorEndpointIndex b) +
      serreCubeGeneratorDegree m j = k := (congrArg (· + serreCubeGeneratorDegree m j) hd).trans hk
  have h₀ := serreCubeRightFace_tensorPair A b n m _ _ k hk
    (serreCubeGenerator A n i) (serreCubeGenerator A m j)
  have h₁ := congrArg (fun x => serreCubeTensorPair A (n + 1) m (serreCubeGeneratorDegree n i)
    (serreCubeGeneratorDegree m j) k hk x (serreCubeGenerator A m j))
    (serreCubeGenerator_point_cast A b n i _ rfl)
  have h₂ := serreCubeTensorPair_cast_left A (n + 1) m hd hsum hk
    (serreCubeGenerator A (n + 1) (i, serreCubeGeneratorEndpointIndex b)) (serreCubeGenerator A m j)
  exact h₀.trans (h₁.trans (h₂.trans (serreCubeTensorPair_generator A (n + 1)
    (i, serreCubeGeneratorEndpointIndex b) m j k hsum)))

end SerrePositivity.KST.SConstruction
