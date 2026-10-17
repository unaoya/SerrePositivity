module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticRawSourceComparison

/-!
# André E1・E2：モニック f/d 源と raw 包の実完備化比較

## 概要

一般モニック f/d 源の実 H⁰ を、同じ係数作用の raw 包およびその実完備化へ比較する。
BS Rem 7.15（著者版 p.62）の raw PD 環との比較の準備。

## 方針

一般 δ 除算の通常テンソル表示、標準 augmentation、実係数制限と完備化の既存比較を再利用する。
原典の Prop 7.11 を使う経路とは異なる、具体的な元の係数作用を保つ計算。

## 規約

この H⁰ 比較にはモニック性・正次数・有限性は不要。高次ホモロジー消滅は別の証明を使う。

## 使われ方

実完備化源の離散性と組み合わせ、元の係数射の完全忠実平坦性を raw PD 環へ移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "β" => deltaDivisionSourceEval E r
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "j" => deltaAdjoinDivisionMap E (MvPolynomial.C d) r
local notation "C₀" => algebraMap A L

/-- 概要：評価βを経由する制限作用と、raw環の標準A作用の恒等線形同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawCoefficientModuleIso :
    (ModuleCat.restrictScalars C₀).obj (MonicPrismaticSourceRawModule D d f) ≅
      ModuleCat.of A Raw := by
  let e : (ModuleCat.restrictScalars C₀).obj (MonicPrismaticSourceRawModule D d f) ≃ₗ[A] Raw :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        rw [RingHom.id_apply, ModuleCat.restrictScalars.smul_def]
        change Raw at x
        change j (β (MvPolynomial.C (MvPolynomial.C a))) * x = a • x
        rw [Algebra.smul_def, deltaDivisionSourceEval_C]
        rfl }
  exact e.toModuleIso

/-- 概要：元のAへの実係数制限後のraw対象を、標準A作用付きraw環の次数零対象へ戻す。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawCoefficientSingleIso :
    MonicPrismaticSourceRawCoefficientObject D d f ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A Raw) :=
  ObjectProperty.isoMk _
    ((derivedRestrictScalarsSingleIso C₀ 0).app (MonicPrismaticSourceRawModule D d f) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso
        (monicPrismaticSourceRawCoefficientModuleIso D d f))

set_option maxHeartbeats 800000 in
-- 元の導来テンソルと二つの係数制限を H⁰ の型に明示して照合するため。
/-- 概要：元の実導来源のH0は、標準A作用付きraw r/d環と線形同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS Rem 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawStandardH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (MonicPrismaticSourceCoefficientObject D d f).obj ≅ ModuleCat.of A Raw :=
  monicPrismaticSourceRawCoefficientH0Iso D d f ≪≫ monicPrismaticSourceRawCoefficientModuleIso D d f

end SerrePositivity.BhattScholze.Andre
