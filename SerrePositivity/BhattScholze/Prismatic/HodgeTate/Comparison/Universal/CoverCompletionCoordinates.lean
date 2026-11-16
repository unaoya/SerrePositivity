module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AssociatedCompletionComparison
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.Construction61Detection
public import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletion
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.Construction61Detection

/-!
# 元の被覆関手と像の二座標完備化の自然な一致

## 概要
元の Construction 6.1 の関手と、像の座標 α(p),α(d) に沿う反復完備化を比較する。

## 方針
α(d)=p*u の単位を明示して座標の同伴性を証明し、標準単位を保つ自然同型へ渡す。

## 規約
比較は導来圏上の指定自然同型であり、複体の射が等しいとは主張しない。

## 使われ方
HT02 の Tot 比較での座標と、元の被覆反映関手の (p,p) を一致させる。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-- 元の被覆射に沿う完備化の二つの像の座標。 -/
abbrev coverImageCoordinates : Fin 2 → Construction61.crystallineCoverRing P :=
  fun j => (Construction61.crystallineCoverMap P).toRingHom (![(p : A), P.generator] j)

/-- 二番目の座標の単位を残して比較すると、二つの像の座標はともに p と同伴。 -/
theorem coverImageCoordinates_associated (j : Fin 2) :
    Associated (coverImageCoordinates P j) (p : Construction61.crystallineCoverRing P) := by
  fin_cases j
  · change Associated ((Construction61.crystallineCoverMap P).toRingHom (p : A)) _
    simpa only [map_natCast] using
      (Associated.refl (p : Construction61.crystallineCoverRing P))
  · obtain ⟨v, hv, _⟩ := (Construction61.crystallineCoverMap P).existsUnique_generator_unit
    change Associated ((Construction61.crystallineCoverMap P).toRingHom P.generator) _
    rw [hv, Construction61.crystallineCover_generator]
    exact (show Associated (p : Construction61.crystallineCoverRing P)
      ((p : Construction61.crystallineCoverRing P) * (v : Construction61.crystallineCoverRing P))
        from ⟨v, rfl⟩).symm

/-- 元の二つの完備底変換模型は、標準単位を保って導来圏で自然に一致する。 -/
def coverImageCompletionNatIso :
    ((ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).mapHomologicalComplex
        (.up ℤ) ⋙ finiteCompletionFunctor (coverImageCoordinates P)) ⋙
          DerivedCategory.Q ≅
      Construction61.completedCoverModelFunctor P ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft
    ((ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).mapHomologicalComplex
      (.up ℤ))
    (associatedFiniteCompletionNatIso (coverImageCoordinates P) (fun _ : Fin 2 => (p : _))
      (coverImageCoordinates_associated P))

/-- 元の射の像の擬同型性は、二つの完備化座標の表示によらない。 -/
theorem coverImageCompletion_quasiIso_iff {K L : Complex A} (f : K ⟶ L) :
    QuasiIso ((finiteCompletionFunctor (coverImageCoordinates P)).map
      (((ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).mapHomologicalComplex
        (.up ℤ)).map f)) ↔
      QuasiIso ((Construction61.completedCoverModelFunctor P).map f) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, ← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact NatIso.isIso_map_iff (coverImageCompletionNatIso P) f

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
