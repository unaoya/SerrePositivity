module
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorDifferential
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorFaces

/-! # 元の全零次数 tensor 生成元の閉性
概要：任意次元の元の cube の零次数 tensor 生成元は、元の実微分で閉じている。
方針：端点挿入の微分再帰で帰納し、辺を含む添字は次数非正性で排除する。
規約：元の生成元と零次数への移送を保持。使われ方：全生成元の HA 微分条件の基底。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の任意次元の cube の零次数 tensor 生成元は、同じ実微分で閉じている。 -/
lemma serreCubeGenerator_zero_d (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (hi : serreCubeGeneratorDegree n i = 0) :
    (serreCubeComplex A n).d 0 1
      (eqToHom (congrArg (fun k => (serreCubeComplex A n).X k) hi)
        (serreCubeGenerator A n i)) = 0 := by
  induction n with
  | zero => exact serreCubeTopCell_zero_d A
  | succ n ih =>
    obtain ⟨i, j⟩ := i
    fin_cases j
    · have hp : serreCubeGeneratorDegree n i = 0 := by
        change serreCubeGeneratorDegree n i + 0 = 0 at hi
        omega
      exact (serreCubeGenerator_point_d A false n i 0 hp).trans
        ((congrArg (fun w => (serreCubeFace A false n 0).hom.f 1 w) (ih i hp)).trans
          (map_zero ((serreCubeFace A false n 0).hom.f 1).hom))
    · have hp : serreCubeGeneratorDegree n i = 0 := by
        change serreCubeGeneratorDegree n i + 0 = 0 at hi
        omega
      exact (serreCubeGenerator_point_d A true n i 0 hp).trans
        ((congrArg (fun w => (serreCubeFace A true n 0).hom.f 1 w) (ih i hp)).trans
          (map_zero ((serreCubeFace A true n 0).hom.f 1).hom))
    · have h := serreCubeGeneratorDegree_freeDimension n i
      change serreCubeGeneratorDegree n i + (-1) = 0 at hi
      omega

end SerrePositivity.KST.SConstruction
