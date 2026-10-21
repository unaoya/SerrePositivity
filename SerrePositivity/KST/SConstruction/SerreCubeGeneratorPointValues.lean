module
public import SerrePositivity.KST.SConstruction.SerreCubeGenerators
public import SerrePositivity.KST.SConstruction.SerreCubeTopFaces

/-! # 元の tensor 生成元の端点挿入・辺保持の値
概要：元の生成元の次数移送を保って、右端への端点挿入・辺保持を回収する。
方針：元の面の斉次評価と元の双次数包含の次数移送を使う。
規約：元の端点・辺・tensor 順を保持。使われ方：各生成元の標準面最高生成元表示。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の端点に対応する元の区間生成元番号。 -/
def serreCubeGeneratorEndpointIndex (b : Bool) : Fin 3 := if b then 1 else 0

/-- 元の端点番号の生成元は、元の同じ右端面の像を指定次数で回収する。 -/
lemma serreCubeGenerator_point_cast (b : Bool) (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (k : ℤ) (hk : serreCubeGeneratorDegree n i = k) :
    (serreCubeFace A b n 0).hom.f k
        (eqToHom (congrArg (fun d => (serreCubeComplex A n).X d) hk)
          (serreCubeGenerator A n i)) =
      eqToHom (congrArg (fun d => (serreCubeComplex A (n + 1)).X d)
        (show serreCubeGeneratorDegree (n + 1) (i, serreCubeGeneratorEndpointIndex b) = k by
          cases b <;> exact (add_zero _).trans hk))
        (serreCubeGenerator A (n + 1) (i, serreCubeGeneratorEndpointIndex b)) := by
  cases b <;> cases hk
  · exact (serreCubeFace_zero_apply A false n _ (serreCubeGenerator A n i)).trans
      (serreCubeGenerator_succ_cast A n i 0 _ (add_zero _)).symm
  · exact (serreCubeFace_zero_apply A true n _ (serreCubeGenerator A n i)).trans
      (serreCubeGenerator_succ_cast A n i 1 _ (add_zero _)).symm

/-- 元の辺を保持した tensor は、元の次の生成元を指定次数で回収する。 -/
lemma serreCubeGenerator_keep_cast (n : ℕ) (i : SerreCubeGeneratorIndex n) (k l : ℤ)
    (hk : serreCubeGeneratorDegree n i = k) (hl : k + (-1) = l) :
    ιTensorObj (serreCubeComplex A n) (serreInterval A) k (-1) l hl
        (eqToHom (congrArg (fun d => (serreCubeComplex A n).X d) hk)
          (serreCubeGenerator A n i) ⊗ₜ[A] serreIntervalEdge A) =
      eqToHom (congrArg (fun d => (serreCubeComplex A (n + 1)).X d)
        (show serreCubeGeneratorDegree (n + 1) (i, 2) = l from
          (congrArg (fun d => d + (-1)) hk).trans hl))
        (serreCubeGenerator A (n + 1) (i, 2)) := by
  cases hk
  exact (serreCubeGenerator_succ_cast A n i 2 l hl).symm

end SerrePositivity.KST.SConstruction
