module

public import SerrePositivity.AlgebraicGeometry.FrobeniusRingDiagram
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechRefinementNaturality

/-!
概要：実際の環の前層の Frobenius 順極限と、被覆の細分の比較を整合させる。
方針：有限交叉への制限は添字の引き戻しであり、既存の細分の自然性・独立性を使う。
規約：整数係数は任意の宇宙で扱い、細分の比較を新しく作り直さない。
使われ方：2e の共通アフィン細分を F8 の実際の環の係数へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite
universe u v
variable {X : Type u} [TopologicalSpace X]
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]

/-- 有限個の開集合の交叉への、反変な添字の関手。 -/
def openCoverCechIndexFunctor (U : ι → Opens X) : Finset ι ⥤ (Opens X)ᵒᵖ where
  obj T := op (cechOpenIntersection U T)
  map f := (homOfLE (cechOpenIntersection_antitone U (leOfHom f))).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- 実際の環の前層を有限交叉上の切断の環の図式に制限する。 -/
def openCoverCechRingDiagram (P : (Opens X)ᵒᵖ ⥤ CommRingCat.{v}) (U : ι → Opens X) :=
  openCoverCechIndexFunctor U ⋙ P

variable (P : (Opens X)ᵒᵖ ⥤ CommRingCat.{v}) (p : ℕ) (hp : p.Prime)
variable (hP : ∀ O, (p : P.obj O) = 0)
variable {Q : (Opens X)ᵒᵖ ⥤ CommRingCat.{v}} {hQ : ∀ O, (p : Q.obj O) = 0}

/-- 有限交叉への制限と実際の環ごとの Frobenius 順極限は同じ係数図式を与える。 -/
theorem openCoverFrobeniusCechDiagram_eq (U : ι → Opens X) :
    openCoverCechDiagram (frobeniusRingDiagram P p hp hP) U =
      frobeniusRingDiagram (openCoverCechRingDiagram P U) p hp
        (fun T ↦ hP (op (cechOpenIntersection U T))) := rfl

/-- 係数の実際の環の射も、有限交叉への制限と Frobenius 順極限の交換に整合する。 -/
theorem openCoverFrobeniusCechCoefficientMap_eq (η : P ⟶ Q) (U : ι → Opens X) :
    openCoverCechCoefficientMap (frobeniusRingDiagramMap p hp hP (hE := hQ) η) U =
      frobeniusRingDiagramMap p hp (fun T ↦ hP (op (cechOpenIntersection U T)))
        (hE := fun T ↦ hQ (op (cechOpenIntersection U T)))
        (Functor.whiskerLeft (openCoverCechIndexFunctor U) η) := rfl

/-- Frobenius 順極限後の細分の射は、元の環の前層の射に自然。 -/
theorem openCoverFrobeniusCechRefinement_naturality
    (η : P ⟶ Q) (U : ι → Opens X) (V : κ → Opens X)
    (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j)) :
    openCoverCechRefinementMap (frobeniusRingDiagram P p hp hP) U V ρ hρ ≫
        fullCechComplexMap
          (openCoverCechCoefficientMap (frobeniusRingDiagramMap p hp hP (hE := hQ) η) V) =
      fullCechComplexMap
          (openCoverCechCoefficientMap (frobeniusRingDiagramMap p hp hP (hE := hQ) η) U) ≫
        openCoverCechRefinementMap (frobeniusRingDiagram Q p hp hQ) U V ρ hρ :=
  openCoverCechRefinementMap_naturality U V ρ hρ
    (frobeniusRingDiagramMap p hp hP (hE := hQ) η)

/-- Frobenius 順極限後も Čech H 上の細分写像は添字の選択によらない。 -/
theorem openCoverFrobeniusCechRefinement_homologyMap_eq
    (U : ι → Opens X) (V : κ → Opens X) (ρ σ : κ → ι)
    (hρ : ∀ j, V j ≤ U (ρ j)) (hσ : ∀ j, V j ≤ U (σ j)) (q : ℕ) :
    HomologicalComplex.homologyMap
        (openCoverCechRefinementMap (frobeniusRingDiagram P p hp hP) U V ρ hρ) q =
      HomologicalComplex.homologyMap
        (openCoverCechRefinementMap (frobeniusRingDiagram P p hp hP) U V σ hσ) q :=
  openCoverCechRefinement_homologyMap_eq (frobeniusRingDiagram P p hp hP) U V ρ σ hρ hσ q

end SerrePositivity.AlgebraicGeometry
