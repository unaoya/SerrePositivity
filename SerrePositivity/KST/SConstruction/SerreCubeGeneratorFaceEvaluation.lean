module
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorFaces
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorPointValues

/-! # 元の全 tensor 生成元の標準面最高生成元による回収
概要：元の全端点・辺 tensor 生成元は、対応する元の標準面の最高生成元像そのもの。
方針：元の面表示の再帰と、元の端点挿入・辺保持の斉次評価を帰納する。
規約：元の Serre 余モノイド射・次数移送・因子順を保持。使われ方：全生成元復元。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の各標準面の最高生成元像は、元の同じ全 tensor 生成元を次数移送で回収する。 -/
lemma serreCubeGenerator_face_top (n : ℕ) (i : SerreCubeGeneratorIndex n) :
    (serreCubeFaceNormal A (serreCubeGeneratorFaceNormal n i)).hom.f
        (-(serreCubeGeneratorFreeDimension n i : ℤ))
        (serreCubeTopCell A (serreCubeGeneratorFreeDimension n i)) =
      eqToHom (congrArg (fun d => (serreCubeComplex A n).X d)
        (serreCubeGeneratorDegree_freeDimension n i)) (serreCubeGenerator A n i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨i, j⟩ := i
    fin_cases j
    · change (serreCubeFace A false n 0).hom.f _
        ((serreCubeFaceNormal A (serreCubeGeneratorFaceNormal n i)).hom.f _
          (serreCubeTopCell A _)) = _
      exact (congrArg (fun w => (serreCubeFace A false n 0).hom.f _ w) (ih i)).trans
        (serreCubeGenerator_point_cast A false n i _ (serreCubeGeneratorDegree_freeDimension n i))
    · change (serreCubeFace A true n 0).hom.f _
        ((serreCubeFaceNormal A (serreCubeGeneratorFaceNormal n i)).hom.f _
          (serreCubeTopCell A _)) = _
      exact (congrArg (fun w => (serreCubeFace A true n 0).hom.f _ w) (ih i)).trans
        (serreCubeGenerator_point_cast A true n i _ (serreCubeGeneratorDegree_freeDimension n i))
    · change (((serreCubeFaceNormal A (serreCubeGeneratorFaceNormal n i)).hom ⊗ₘ
          𝟙 (serreInterval A)).f (-((serreCubeGeneratorFreeDimension n i + 1 : ℕ) : ℤ)))
        (serreCubeTopCell A (serreCubeGeneratorFreeDimension n i + 1)) = _
      have hs := congrArg (fun w =>
        (((serreCubeFaceNormal A (serreCubeGeneratorFaceNormal n i)).hom ⊗ₘ
          𝟙 (serreInterval A)).f (-((serreCubeGeneratorFreeDimension n i + 1 : ℕ) : ℤ))) w)
        (serreCubeTopCell_succ A (serreCubeGeneratorFreeDimension n i))
      have ht := tensorMap_apply
        (serreCubeFaceNormal A (serreCubeGeneratorFaceNormal n i)).hom (𝟙 (serreInterval A))
        (-(serreCubeGeneratorFreeDimension n i : ℤ)) (-1)
        (-((serreCubeGeneratorFreeDimension n i + 1 : ℕ) : ℤ)) (by omega)
        (serreCubeTopCell A (serreCubeGeneratorFreeDimension n i)) (serreIntervalEdge A)
      exact hs.trans (ht.trans
        ((congrArg (fun w => ιTensorObj (serreCubeComplex A n) (serreInterval A)
          (-(serreCubeGeneratorFreeDimension n i : ℤ)) (-1)
          (-((serreCubeGeneratorFreeDimension n i + 1 : ℕ) : ℤ)) (by omega)
          (w ⊗ₜ[A] serreIntervalEdge A)) (ih i)).trans
          (serreCubeGenerator_keep_cast A n i _ _
            (serreCubeGeneratorDegree_freeDimension n i) (by omega))))

end SerrePositivity.KST.SConstruction
