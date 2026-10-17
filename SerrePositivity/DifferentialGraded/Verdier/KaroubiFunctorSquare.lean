module
public import SerrePositivity.DifferentialGraded.Verdier.ScalarExtensionTria

/-! # tria・Perf 間の比較正方形の Karoubi 延長 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents

section General
variable {C : Type*} [Category* C] {E : Type*} [Category* E] {T : Type*} [Category* T]
  (F : C ⥤ E) (G : E ⥤ T)

def karoubiFunctorCompositionIso :
    (functorExtension₂ C E).obj F ⋙ (functorExtension₂ E T).obj G ≅
      (functorExtension₂ C T).obj (F ⋙ G) := Iso.refl _

/-- 元の正方形を、両経路の Karoubi 延長の正方形へ送る。 -/
def karoubiFunctorSquare {E' : Type*} [Category* E'] {F' : C ⥤ E'} {G' : E' ⥤ T}
    (e : F ⋙ G ≅ F' ⋙ G') :
    (functorExtension₂ C E).obj F ⋙ (functorExtension₂ E T).obj G ≅
      (functorExtension₂ C E').obj F' ⋙ (functorExtension₂ E' T).obj G' :=
  karoubiFunctorCompositionIso F G ≪≫ (functorExtension₂ C T).mapIso e ≪≫
    (karoubiFunctorCompositionIso F' G').symm
end General

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- finite cell の Karoubi–Perf 比較は元の tria の包含を延長する。 -/
def triaKaroubiPerfectFactors :
    toKaroubi (TriaCategory A D) ⋙ finiteCellKaroubiToPerfect A D Set.univ ≅
      triaToPerfect A D :=
  ((whiskeringRight _ _ _).obj (modulePerfect A D).ι).preimageIso
    (X := toKaroubi (TriaCategory A D) ⋙ finiteCellKaroubiToPerfect A D Set.univ)
    (Y := triaToPerfect A D) (finiteCellKaroubiRealization_fac A D Set.univ)

variable {A' : Type u} [CommRing A'] (E : Type w) [DGCategory A' E] [Small.{u} E]
  (G : TriaCategory A D ⥤ TriaCategory A' E)
  (T : PerfectModuleCategory A D ⥤ PerfectModuleCategory A' E)

/-- 実際の tria–Perf 正方形から、既存 Karoubi–Perf 同値の自然性を得る。 -/
def triaKaroubiPerfectSquare
    (e : G ⋙ triaToPerfect A' E ≅ triaToPerfect A D ⋙ T) :
    (functorExtension₂ (TriaCategory A D) (TriaCategory A' E)).obj G ⋙
        finiteCellKaroubiToPerfect A' E Set.univ ≅
      finiteCellKaroubiToPerfect A D Set.univ ⋙ T :=
  whiskeringLeftObjToKaroubiFullyFaithful.preimageIso
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight
        ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app G) _ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft G (triaKaroubiPerfectFactors A' E) ≪≫ e ≪≫
      isoWhiskerRight (triaKaroubiPerfectFactors A D).symm T ≪≫ Functor.associator _ _ _)

namespace DGQuotient
variable {A D} (φ : A →+* A') (S : Set D)

/-- 係数変更の tria 制限を完備化すると、元の実際の Perf 係数変更となる。 -/
def quotientScalarKaroubiPerfectSquare :
    (functorExtension₂ _ _).obj (quotientScalarTriaFunctor φ S) ⋙
        finiteCellKaroubiToPerfect A' (QuotientObject (ScalarExtension.DGBaseChange φ D) S)
          Set.univ ≅
      finiteCellKaroubiToPerfect A (QuotientObject D S) Set.univ ⋙
        quotientScalarPerfectFunctor φ D S :=
  triaKaroubiPerfectSquare A (QuotientObject D S) _ _ _
    (quotientScalarTriaPerfectSquare φ S)
end DGQuotient
end SerrePositivity.DifferentialGraded
