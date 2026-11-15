module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FixedTorBounds
public import SerrePositivity.HomologicalAlgebra.CochainTensorScalarCone

/-!
# スカラー錐と有限 Koszul の自然な交換

## 概要
元のスカラー錐関手と有限 Koszul 関手を交換する自然同型を作る。

## 方針
スカラー錐を単位のスカラー錐とのテンソルで表示し、Mathlib の tensorLeftTensor で自然に交換する。

## 規約
元の関手とその射を保つ。個別に選んだ対象同型の自然性を仮定しない。

## 使われ方
BS 著者版 Lemma 4.22 の、有限 Koszul による標準完備化単位の簡約。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
variable {R : Type u} [CommRing R]

/-- 元の単位複体のスカラー錐。 -/
abbrev scalarConeCoefficient (a : R) : Complex R :=
  CochainComplex.mappingCone (smulId a (cochainTensorUnit (R := R)))

/-- 元のスカラー錐を、単位のスカラー錐とのテンソルとして自然に表示する。 -/
def scalarConeTensorNatIso (a : R) :
    cochainTensorFixedLeft (scalarConeCoefficient a) ≅ scalarConeFunctor a :=
  NatIso.ofComponents (cochainTensorUnitScalarConeIso a)
    (fun f => cochainTensorUnitScalarConeIso_naturality a f)

/-- 二つのスカラー錐の交換。自然性は全て元の関手の自然同型から受け取る。 -/
def scalarConeSwapNatIso (a b : R) :
    scalarConeFunctor b ⋙ scalarConeFunctor a ≅ scalarConeFunctor a ⋙ scalarConeFunctor b :=
  Functor.isoWhiskerRight (scalarConeTensorNatIso b).symm (scalarConeFunctor a) ≪≫
    Functor.isoWhiskerLeft (cochainTensorFixedLeft (scalarConeCoefficient b))
      (scalarConeTensorNatIso a).symm ≪≫
    (tensorLeftTensor (scalarConeCoefficient a) (scalarConeCoefficient b)).symm ≪≫
    (tensoringLeft (Complex R)).mapIso
      (cochainTensorSymmetry (scalarConeCoefficient a) (scalarConeCoefficient b)) ≪≫
    tensorLeftTensor (scalarConeCoefficient b) (scalarConeCoefficient a) ≪≫
    Functor.isoWhiskerLeft (cochainTensorFixedLeft (scalarConeCoefficient a))
      (scalarConeTensorNatIso b) ≪≫
    Functor.isoWhiskerRight (scalarConeTensorNatIso a) (scalarConeFunctor b)

/-- 有限 Koszul とスカラー錐の自然な交換。 -/
def scalarConeKoszulNatIso (a : R) : ∀ {r : ℕ} (x : Fin r → R),
    koszulFunctor x ⋙ scalarConeFunctor a ≅ scalarConeFunctor a ⋙ koszulFunctor x
  | 0, _ => Functor.leftUnitor (scalarConeFunctor a) ≪≫
      (Functor.rightUnitor (scalarConeFunctor a)).symm
  | r+1, x =>
    Functor.associator (koszulFunctor (Fin.init x)) (scalarConeFunctor (x (Fin.last r)))
      (scalarConeFunctor a) ≪≫
    Functor.isoWhiskerLeft (koszulFunctor (Fin.init x)) (scalarConeSwapNatIso a (x (Fin.last r))) ≪≫
    (Functor.associator (koszulFunctor (Fin.init x)) (scalarConeFunctor a)
      (scalarConeFunctor (x (Fin.last r)))).symm ≪≫
    Functor.isoWhiskerRight (scalarConeKoszulNatIso a (Fin.init x))
      (scalarConeFunctor (x (Fin.last r))) ≪≫
    Functor.associator (scalarConeFunctor a) (koszulFunctor (Fin.init x))
      (scalarConeFunctor (x (Fin.last r)))

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
