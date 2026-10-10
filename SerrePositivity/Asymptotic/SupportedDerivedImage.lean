module

public import SerrePositivity.Asymptotic.SequenceDerived
public import SerrePositivity.Asymptotic.SequenceHomology
public import SerrePositivity.Asymptotic.SupportedRankQuotient
public import SerrePositivity.CategoryTheory.FamilyTriangulatedImage

/-!
# 支持つき自由列から導来対象の族への像

既存の完全忠実性を支持部分圏に制限し、成分ごとの完全三角形から
共通有界な支持つき自由列の代表を組み立てるための閉包性を得る。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}
  [HasDerivedCategory (ModuleCat.{u} R)] {e : ℕ} (z : Fin e → R)

/-- 一様に支持された自由列の第 n 段を導来圏に送る三角関手。 -/
noncomputable abbrev supportedDerivedEvaluation (n : ℕ) :
    (supportedSequence (s := s) z).FullSubcategory ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (supportedSequence z).ι ⋙ boundedHomotopyInclusion _ ⋙
    (FreeSequence.evaluation n).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

/-- 各段の導来射は、支持つき自由列の一つの射として同時に持ち上がる。 -/
lemma supportedDerivedEvaluation_full
    (X Y : (supportedSequence (s := s) z).FullSubcategory)
    (f : ∀ n, (supportedDerivedEvaluation z n).obj X ⟶ (supportedDerivedEvaluation z n).obj Y) :
    ∃ g : X ⟶ Y, ∀ n, (supportedDerivedEvaluation z n).map g = f n := by
  obtain ⟨g, hg⟩ := (pointwiseDerived (R := R) (s := s)).map_surjective
    (show pointwiseDerived.obj X.obj ⟶ pointwiseDerived.obj Y.obj from f)
  exact ⟨⟨g⟩, fun n ↦ congrFun hg n⟩

/-- 各段で与えた導来同型は、元の支持つき自由列の同型に持ち上がる。 -/
noncomputable def supportedDerivedEvaluation_preimageIso
    (X Y : (supportedSequence (s := s) z).FullSubcategory)
    (i : ∀ n, (supportedDerivedEvaluation z n).obj X ≅ (supportedDerivedEvaluation z n).obj Y) :
    X ≅ Y :=
  ObjectProperty.isoMk _ ((pointwiseDerived (R := R) (s := s)).preimageIso (Pi.isoMk i))

/-- 支持つき列のホモロジーと段ごとの導来ホモロジーとの比較。 -/
noncomputable def supportedDerivedHomologyIso
    (X : (supportedSequence (s := s) z).FullSubcategory) (q : ℤ) :
    Discrete.functor (fun n ↦ (DerivedCategory.homologyFunctor (ModuleCat R) q).obj
      ((supportedDerivedEvaluation z n).obj X)) ≅ (sequenceHomology q).obj X.obj :=
  Discrete.natIso (fun n ↦ (DerivedCategory.homologyFunctorFactorsh (ModuleCat R) q).app
    (((FreeSequence.evaluation n.as).mapHomotopyCategory (.up ℤ)).obj X.obj.obj))

/-- 導来対象の族が、共通有界な支持つき自由列で表せるという条件。 -/
abbrev supportedDerivedImage := familyEssImage (supportedDerivedEvaluation (s := s) z)

/-- 支持つき自由列による代表は、成分ごとの完全三角形で拡大できる。 -/
lemma supportedDerivedImage_extension
    (T : ℕ → Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : ∀ n, T n ∈ distTriang _)
    (h₁ : supportedDerivedImage (s := s) z (fun n ↦ (T n).obj₁))
    (h₃ : supportedDerivedImage (s := s) z (fun n ↦ (T n).obj₃)) :
    supportedDerivedImage (s := s) z (fun n ↦ (T n).obj₂) :=
  familyEssImage_extension _ (supportedDerivedEvaluation_full z) T hT h₁ h₃

end SerrePositivity.Asymptotic
