module
public import SerrePositivity.KST.SConstruction.SerreCubeAppendEdgeDifferential
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorPointValues

/-! # 元の全端点・辺 tensor 生成元の微分再帰
概要：任意の元の生成元への端点・辺付加の微分を、前段の実微分と右端二面で回収する。
方針：元の端点挿入・辺保持の次数移送付き表示と全斉次元の微分式を合成する。
規約：元の生成元・次数移送・tensor 順を保持。使われ方：全生成元上の HA 微分条件。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の任意の端点付加生成元の微分は、前段の元の微分への同じ端点挿入。 -/
lemma serreCubeGenerator_point_d (b : Bool) (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (p : ℤ) (hp : serreCubeGeneratorDegree n i = p) :
    (serreCubeComplex A (n + 1)).d p (p + 1)
        (eqToHom (congrArg (fun k => (serreCubeComplex A (n + 1)).X k)
          (show serreCubeGeneratorDegree (n + 1) (i, serreCubeGeneratorEndpointIndex b) = p by
            cases b <;> exact (add_zero _).trans hp))
          (serreCubeGenerator A (n + 1) (i, serreCubeGeneratorEndpointIndex b))) =
      (serreCubeFace A b n 0).hom.f (p + 1) ((serreCubeComplex A n).d p (p + 1)
        (eqToHom (congrArg (fun k => (serreCubeComplex A n).X k) hp)
          (serreCubeGenerator A n i))) :=
  (congrArg (fun w => (serreCubeComplex A (n + 1)).d p (p + 1) w)
    (serreCubeGenerator_point_cast A b n i p hp).symm).trans
      (serreCubeEndpoint_d A b n p _)

/-- 元の任意の辺付加生成元の微分は、前段の微分への辺付加と元の右端二面差。 -/
lemma serreCubeGenerator_keep_d (n : ℕ) (i : SerreCubeGeneratorIndex n)
    (p : ℤ) (hp : serreCubeGeneratorDegree n i = p) :
    (serreCubeComplex A (n + 1)).d (p - 1) p
        (eqToHom (congrArg (fun k => (serreCubeComplex A (n + 1)).X k)
          (show serreCubeGeneratorDegree (n + 1) (i, 2) = p - 1 from
            (congrArg (fun k => k + (-1)) hp).trans (by omega)))
          (serreCubeGenerator A (n + 1) (i, 2))) =
      serreCubeAppendEdge A n (p + 1) p (by omega) ((serreCubeComplex A n).d p (p + 1)
        (eqToHom (congrArg (fun k => (serreCubeComplex A n).X k) hp) (serreCubeGenerator A n i))) +
      p.negOnePow •
        ((serreCubeFace A true n 0).hom.f p
            (eqToHom (congrArg (fun k => (serreCubeComplex A n).X k) hp)
              (serreCubeGenerator A n i)) -
          (serreCubeFace A false n 0).hom.f p
            (eqToHom (congrArg (fun k => (serreCubeComplex A n).X k) hp)
              (serreCubeGenerator A n i))) :=
  (congrArg (fun w => (serreCubeComplex A (n + 1)).d (p - 1) p w)
    (serreCubeGenerator_keep_cast A n i p (p - 1) hp (by omega)).symm).trans
      (serreCubeAppendEdge_d A n p _)

end SerrePositivity.KST.SConstruction
