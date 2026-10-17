module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleIndependence
public import SerrePositivity.DifferentialGraded.Derived.BimoduleSemifreeComposeComparison

/-! # 制限後に選ぶsemifree解像度からの中間圏導来比較の独立性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory

/-- 指定semifree解像度を、既存の局所Hom条件の下で右K-flat対象として読む。 -/
def BimoduleSemifreeResolution.toRightKFlat (A : Type u) [CommRing A]
    (D : Type z) [DGCategory A D] [Small.{u} D]
    (E : Type t) [DGCategory A E] [Small.{u} E] {M : BimoduleCategory A D E}
    (R : BimoduleSemifreeResolution A D E M) (hE : localHomKFlat A E) :
    BimoduleTensor.RightKFlatBimoduleCategory A D E :=
  ⟨R.obj, R.rightRelativeKFlat A D E hE⟩

namespace BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)
  (R S : BimoduleSemifreeResolution A D E
    ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))

/-- 制限後の任意の二つのsemifree解像度による、実際の導来比較射の一致。 -/
lemma derivedMiddleRestrictionComparison_semifree_independent (P : BimoduleCategory A B C) :
    derivedMiddleRestrictionComparison A B C D E F hE P Q
        (S.toRightKFlat A D E hE) S.π S.quasiIso =
      derivedMiddleRestrictionComparison A B C D E F hE P Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso := by
  let r : R.toRightKFlat A D E hE ⟶ S.toRightKFlat A D E hE :=
    ObjectProperty.homMk (R.comparison S)
  apply derivedMiddleRestrictionComparison_eq_of_squares A B C D E F hE Q
    (R.toRightKFlat A D E hE) (S.toRightKFlat A D E hE) R.π S.π R.quasiIso S.quasiIso r
    (R.comparison_fac S).symm P
  let P₀ := (BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P
  have hc := BimoduleSemifreeResolution.composeAfter_comparison_fac A B D E P₀ R S
  dsimp only [middleRestrictionResolvedMap]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ (bimoduleToDerived A B E).map
      (middleRestrictionComparisonMap A B C D E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q.obj))) hc)

lemma derivedMiddleRestrictionComparisonFamily_semifree_independent :
    derivedMiddleRestrictionComparisonFamily A B C D E F hE Q
        (S.toRightKFlat A D E hE) S.π S.quasiIso =
      derivedMiddleRestrictionComparisonFamily A B C D E F hE Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso := by
  apply NatTrans.ext
  funext P
  rw [derivedMiddleRestrictionComparisonFamily_app, derivedMiddleRestrictionComparisonFamily_app]
  exact derivedMiddleRestrictionComparison_semifree_independent A B C D E F hE Q R S P

/-- 前因子の全導来圏上の自然変換も、選んだ制限後semifree解像度によらない。 -/
lemma derivedMiddleRestrictionComparisonLocalized_semifree_independent :
    derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q
        (S.toRightKFlat A D E hE) S.π S.quasiIso =
      derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  rw [derivedMiddleRestrictionComparisonLocalized_app,
    derivedMiddleRestrictionComparisonLocalized_app,
    derivedMiddleRestrictionComparison_semifree_independent A B C D E F hE Q R S P]

omit S in
/-- 任意の制限後semifree解像度による射は、既存標準解像度を使う比較射と一致する。 -/
lemma derivedMiddleRestrictionComparison_semifree_eq_canonical (P : BimoduleCategory A B C) :
    derivedMiddleRestrictionComparison A B C D E F hE P Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso =
      derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q :=
  (derivedMiddleRestrictionComparison_semifree_independent A B C D E F hE Q R
    (bimoduleCanonicalSemifreeResolution A D E _) P).symm

/-- 制限後の標準semifree解像度を使い、前因子の全導来圏上で自然な比較。 -/
def derivedMiddleRestrictionCanonicalLocalized :
    middleDerivedSourceLift A B C D E F hE Q ⟶
      (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj) :=
  derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q
    (rightKFlatResolutionObj A D E hE
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))
    (bimoduleCanonicalSemifreeResolution A D E _).π
    (bimoduleCanonicalSemifreeResolution A D E _).quasiIso

omit S in
lemma derivedMiddleRestrictionComparisonLocalized_semifree_eq_canonical :
    derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso =
      derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q :=
  (derivedMiddleRestrictionComparisonLocalized_semifree_independent A B C D E F hE Q R
    (bimoduleCanonicalSemifreeResolution A D E _)).symm

end BimoduleTensor
end SerrePositivity.DifferentialGraded
