module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaAxes
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaPairNaturality
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLanePoints
public import SerrePositivity.Spectra.Pointed.ReducedPair

/-!
# 指定された Γ の積を smash へ降ろす

DAG XIII §2.2 のスペクトル構造射の前段。零基点と二つの軸を同時に保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

/-- Γ の零基点を持つ対象。 -/
abbrev gammaPointed (K : Complex A) : PointedSimplicialSet.{u} :=
  (modulePointedFunctor A).obj (gammaModule A K)

/-- 同じ二項評価は、どちらの変数の零基点も潰す。 -/
def gammaReducedPair (K L : Complex A) :
    PointedObject.ReducedPairMap (gammaPointed A K) (gammaPointed A L)
      (gammaPointed A (K ⊗ L)) :=
  ⟨gammaPair A K L, by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact gammaPair_zero_left A K L n.unop x.2, by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact gammaPair_zero_right A K L n.unop x.1⟩

/-- 指定 Γ の二項評価は、直積の零基点を保つ。 -/
def gammaPointedPair (K L : Complex A) :
    PointedObject.prod (gammaPointed A K) (gammaPointed A L) ⟶
      gammaPointed A (K ⊗ L) :=
  PointedObject.reducedPairPointed (gammaReducedPair A K L)

lemma gammaPointedPair_axisLeft (K L : Complex A) :
    PointedObject.axisLeft (gammaPointed A K) (gammaPointed A L) ≫
      gammaPointedPair A K L = 0 :=
  PointedObject.reducedPairPointed_axisLeft _

lemma gammaPointedPair_axisRight (K L : Complex A) :
    PointedObject.axisRight (gammaPointed A K) (gammaPointed A L) ≫
      gammaPointedPair A K L = 0 :=
  PointedObject.reducedPairPointed_axisRight _

/-- 同じ二項評価を、二つの軸を潰した実 smash へ降ろした射。 -/
def gammaSmashPair (K L : Complex A) :
    PointedObject.smash (gammaPointed A K) (gammaPointed A L) ⟶
      gammaPointed A (K ⊗ L) :=
  PointedObject.smashDesc (gammaPointedPair A K L)
    (gammaPointedPair_axisLeft A K L) (gammaPointedPair_axisRight A K L)

/-- 商へ引き戻すと、元の指定 Γ の積である。 -/
lemma gammaSmashPair_quotient (K L : Complex A) :
    PointedObject.smashQuotient (gammaPointed A K) (gammaPointed A L) ≫
      gammaSmashPair A K L = gammaPointedPair A K L :=
  PointedObject.smashQuotient_desc ..

end SerrePositivity.EInfinity.PowerOperation
