module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseAlgebra
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion
public import SerrePositivity.HomologicalAlgebra.DerivedHomologyLinear
public import SerrePositivity.HomologicalAlgebra.LinearFunctorScalarCone
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic

/-!
# 射影的な模型の各項完備化と Koszul 複体

## 概要
各項の H⁰ 完備化の線形性、係数制限との自然な比較、射影的な模型の擬同型の保存。
## 方針
実導来完備化の普遍性で線形性を示し、既存の係数制限の比較を H⁰ に通す。
射影的な模型の擬同型はホモトピー同値として各項完備化へ送る。
## 規約
BS 著者版 Proposition 7.10 の有限 T の完備化への入力。
完備化するスカラーの正則性を仮定しない。
## 使われ方
係数環上で分裂する有限根関係の Koszul 分解を完備化する。
-/

public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (a : R)

/-- 実導来完備化は係数環上線形な関手。 -/
instance derivedComplexCompletionFunctor_linear : (derivedComplexCompletionFunctor R a).Linear R where
  map_smul {X Y} f r := by
    let F := derivedComplexCompletionFunctor R a
    let η := derivedComplexCompletionUnit R a
    apply (derivedComplexCompletionHomEquiv R a X (F.obj Y)
      (derivedComplexCompletionFunctor_isComplete R a Y)).injective
    change η.app X ≫ F.map (r • f) = η.app X ≫ (r • F.map f)
    calc
      _ = (r • f) ≫ η.app Y := (η.naturality (r • f)).symm
      _ = r • (f ≫ η.app Y) := by simp
      _ = r • (η.app X ≫ F.map f) := congrArg (fun g => r • g) (η.naturality f)
      _ = _ := by simp

/-- 加群の各項 H⁰ 完備化も係数環上線形。 -/
instance moduleCompletionH0Functor_linear : (moduleCompletionH0Functor R a).Linear R := by
  dsimp only [moduleCompletionH0Functor]
  infer_instance

variable {R} {S : Type u} [CommRing S] (φ : R →+* S)

/-- 概要：各項の H⁰ 完備化は係数制限と自然に可換。
方針：single、実導来完備化、ホモロジーの既存の制限比較を合成する。
規約：BS 著者版 Proposition 7.10 の通常の加群の模型。平坦性や正則性は不要。
使われ方：係数環上の分裂を、関係を持つ代数上の Koszul 複体の完備化へ移す。 -/
def moduleCompletionH0RestrictionIso :
    ModuleCat.restrictScalars φ ⋙ moduleCompletionH0Functor R a ≅
      moduleCompletionH0Functor S (φ a) ⋙ ModuleCat.restrictScalars φ := by
  dsimp only [moduleCompletionH0Functor, moduleObjectFunctor]
  exact Functor.isoWhiskerRight (derivedRestrictScalarsSingleIso φ 0).symm
      (derivedComplexCompletionFunctor R a ⋙ DerivedCategory.homologyFunctor (ModuleCat R) 0) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleCat S) 0)
      (Functor.isoWhiskerRight (derivedCompletionRestrictionIso φ a)
        (DerivedCategory.homologyFunctor (ModuleCat R) 0)) ≪≫
    Functor.isoWhiskerLeft
      (DerivedCategory.singleFunctor (ModuleCat S) 0 ⋙ derivedComplexCompletionFunctor S (φ a))
      (derivedRestrictScalarsHomologyIso φ 0)


/-- 概要：K-projective な二つの模型の擬同型は各項 H⁰ 完備化で保たれる。
方針：擬同型をホモトピー同値とし、既存の加法的な関手の保存性を適用する。
規約：BS 著者版 Proposition 7.10 の有限分解への適用。スカラー正則性は不要。
使われ方：係数環上で射影的な有限根関係の分解の完備化。 -/
theorem moduleCompletionH0Functor_map_quasiIso_of_KProjective
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [QuasiIso f]
    [K.IsKProjective] [L.IsKProjective] :
    QuasiIso (((moduleCompletionH0Functor R a).mapHomologicalComplex (.up ℤ)).map f) := by
  have h := (CochainComplex.IsKProjective.quasiIso_iff f).mp inferInstance
  exact homotopyEquivalences_le_quasiIso _ _ _
    ((moduleCompletionH0Functor R a).homotopyEquivalences_mapHomologicalComplex_map f h)

end SerrePositivity.DerivedCompletion

namespace SerrePositivity
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R]

/-- 線形な加法関手は任意の有限列の Koszul 操作と可換。 -/
def linearFunctorKoszulOnIso (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    [F.Additive] [F.Linear R] : ∀ {n : ℕ} (x : Fin n → R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ),
    (F.mapHomologicalComplex _).obj (koszulComplexOn x K) ≅
      koszulComplexOn x ((F.mapHomologicalComplex _).obj K)
  | 0, _, _ => Iso.refl _
  | n + 1, x, K =>
    linearFunctorScalarConeIso F (x (Fin.last n)) (koszulComplexOn (Fin.init x) K) ≪≫
      (scalarConeFunctor (x (Fin.last n))).mapIso (linearFunctorKoszulOnIso F (Fin.init x) K)

end SerrePositivity
