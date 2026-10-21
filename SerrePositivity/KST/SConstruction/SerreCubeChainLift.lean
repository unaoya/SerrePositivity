module
public import SerrePositivity.KST.SConstruction.SerreCubeDegreeValuesEquiv

/-! # 元の全生成元値と微分条件から実鎖射を復元
概要：元の全 tensor 生成元に与えた値が元の微分と可換なら、同じ元の cube から鎖射を作る。
方針：元の次数線形復元と生成元判定で微分可換性を全次数の射等号へ延長する。
規約：元の微分を条件とし、別模型や追加公理を使わない。使われ方：HA からの逆 Hom 射。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の全生成元値が元の微分と可換なら、元の同じ Serre cube からの鎖射を復元する。 -/
def serreCubeChainLift (n : ℕ) (K : Complex A)
    (v : ∀ k : ℤ, ∀ i : SerreCubeGeneratorIndex n, serreCubeGeneratorDegree n i = k → K.X k)
    (hd : ∀ (k : ℤ) (i : SerreCubeGeneratorIndex n) (hi : serreCubeGeneratorDegree n i = k),
      K.d k (k + 1) (v k i hi) =
        serreCubeDegreeLift A n (k + 1) (K.X (k + 1)) (v (k + 1))
          ((serreCubeComplex A n).d k (k + 1)
            (eqToHom (congrArg (fun d => (serreCubeComplex A n).X d) hi)
              (serreCubeGenerator A n i)))) : serreCubeComplex A n ⟶ K where
  f k := serreCubeDegreeLift A n k (K.X k) (v k)
  comm' k l hkl := by
    have hl : k + 1 = l := hkl
    subst l
    apply serreCube_degree_hom_ext A n k
    intro i hi
    exact (congrArg (fun w => K.d k (k + 1) w)
      (serreCubeDegreeLift_generator A n k (K.X k) (v k) i hi)).trans (hd k i hi)

/-- 元の実鎖射の復元は、元の全生成元に指定した同じ値を回収する。 -/
lemma serreCubeChainLift_generator (n : ℕ) (K : Complex A)
    (v : ∀ k : ℤ, ∀ i : SerreCubeGeneratorIndex n, serreCubeGeneratorDegree n i = k → K.X k)
    (hd) (k : ℤ) (i : SerreCubeGeneratorIndex n) (hi : serreCubeGeneratorDegree n i = k) :
    (serreCubeChainLift A n K v hd).f k
        (eqToHom (congrArg (fun d => (serreCubeComplex A n).X d) hi) (serreCubeGenerator A n i)) =
      v k i hi :=
  serreCubeDegreeLift_generator A n k (K.X k) (v k) i hi

/-- 元の全生成元値を回収する鎖射は、元の同じ復元鎖射に一致する。 -/
lemma serreCubeChainLift_eq (n : ℕ) (K : Complex A)
    (v : ∀ k : ℤ, ∀ i : SerreCubeGeneratorIndex n, serreCubeGeneratorDegree n i = k → K.X k)
    (hd) (f : serreCubeComplex A n ⟶ K)
    (hf : ∀ i : SerreCubeGeneratorIndex n,
      v (serreCubeGeneratorDegree n i) i rfl =
        f.f (serreCubeGeneratorDegree n i) (serreCubeGenerator A n i)) :
    serreCubeChainLift A n K v hd = f := by
  apply serreCube_generator_hom_ext A n
  intro i
  exact (serreCubeChainLift_generator A n K v hd _ i rfl).trans (hf i)

end SerrePositivity.KST.SConstruction
