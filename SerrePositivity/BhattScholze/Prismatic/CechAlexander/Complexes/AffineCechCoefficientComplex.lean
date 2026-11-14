module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.AffineCechPrismBaseChange
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Complexes.CechAlexanderComplex
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps

/-!
# affine Čech 模型の係数変更の余鎖写像

## 概要
既存の係数変更の厳密な自然性を、余単体的代数と交代余面複体の射としてまとめる。
## 方針
全単体射について証明済みの affineEnvelopeCoefficientMap_natural を使う。
## 規約
BS 著者版 Remark 4.19。標的の係数環は基底の prism 射で制限する。
## 使われ方
項ごとの完備底変換と通常の複体の構造射の両立。
-/

public noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {P' : OrientedPrism p B} (f : OrientedPrism.Hom P P')
variable {r : ℕ} {κ κ' : Cardinal.{u}}
variable (U : ∀ n, AffineEnvelopeTerm P r n κ) (V : ∀ n, AffineEnvelopeTerm P' r n κ')

/-- 概要：係数変更は基底の下の余単体的環の自然変換。
方針：既存の係数変更の仕様と自然性を使う。
規約：BS 著者版 Remark 4.19。使われ方：交代余面複体への係数変更。 -/
def affineCechCoefficientTransformation :
    polyCosimplicialAlgebraOfAffineTerms P U ⟶
      polyCosimplicialAlgebraOfAffineTerms P' V ⋙ Under.map (CommRingCat.ofHom f.toRingHom) where
  app n := Under.homMk (CommRingCat.ofHom (affineEnvelopeCoefficientMap f (U n.len) (V n.len))) (by
    apply CommRingCat.hom_ext
    exact (affineEnvelopeCoefficientMap_spec f (U n.len) (V n.len)).2.1)
  naturality {m n} θ := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    exact affineEnvelopeCoefficientMap_natural f (U n.len) (V n.len) (U m.len) (V m.len) θ

/-- Remark 4.19：係数変更から得る交代余面複体の実際の余鎖写像。 -/
def affineCechCoefficientCochainMap :
    (alternatingCofaceMapComplex (ModuleCat.{u} A)).obj
      (polyCosimplicialAlgebraOfAffineTerms P U ⋙ Cech.underToModule (CommRingCat.of A)) ⟶
    (alternatingCofaceMapComplex (ModuleCat.{u} A)).obj
      (polyCosimplicialAlgebraOfAffineTerms P' V ⋙ Under.map (CommRingCat.ofHom f.toRingHom) ⋙
        Cech.underToModule (CommRingCat.of A)) :=
  (alternatingCofaceMapComplex _).map
    (Functor.whiskerRight (affineCechCoefficientTransformation f U V)
      (Cech.underToModule (CommRingCat.of A)))

end SerrePositivity.BhattScholze.Prismatic
