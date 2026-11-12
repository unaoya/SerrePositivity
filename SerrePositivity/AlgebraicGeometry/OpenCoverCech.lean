module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor
public import Mathlib.Topology.Sheaves.Presheaf

/-!
概要：開集合の前層から Čech の有限交叉の図式を作り、細分の制限を与える。
方針：開集合の交叉の包含を反変前層に適用する。
規約：長さ零の交叉は全空間。被覆性・アフィン性はここでは仮定しない。
使われ方：アフィン被覆の共通細分における自然な比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace
universe u v
variable {X : Type u} [TopologicalSpace X] {R : Type v} [CommRing R]
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]

/-- 有限個の開集合の交叉。空交叉は全空間。 -/
def cechOpenIntersection (U : ι → Opens X) (T : Finset ι) : Opens X :=
  ⨅ i ∈ T, U i

/-- 添字集合が増えると交叉は小さくなる。 -/
theorem cechOpenIntersection_antitone (U : ι → Opens X) {T S : Finset ι}
    (h : T ⊆ S) : cechOpenIntersection U S ≤ cechOpenIntersection U T := by
  apply le_iInf
  intro i
  apply le_iInf
  intro hi
  exact iInf_le_of_le i (iInf_le_of_le (h hi) le_rfl)

/-- 前層を、有限交叉上の切断の共変な係数図式と見る。 -/
def openCoverCechDiagram (P : (Opens X)ᵒᵖ ⥤ ModuleCat R) (U : ι → Opens X) :
    Finset ι ⥤ ModuleCat R where
  obj T := P.obj (Opposite.op (cechOpenIntersection U T))
  map {T S} h := P.map (homOfLE (cechOpenIntersection_antitone U (leOfHom h))).op
  map_id T := by
    convert P.map_id (Opposite.op (cechOpenIntersection U T)) using 1
  map_comp f g := by
    rw [← P.map_comp]
    congr 1

/-- タプルに沿う細分の包含。重複した添字も許す。 -/
theorem cechOpenIntersection_refinement (U : ι → Opens X) (V : κ → Opens X)
    (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j)) {k : ℕ} (t : Fin k → κ) :
    cechOpenIntersection V (cechTupleSupport t) ≤
      cechOpenIntersection U (cechTupleSupport (ρ ∘ t)) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro hi
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hi
  exact (iInf_le_of_le (t a) (iInf_le_of_le
    (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩) le_rfl)).trans (hρ (t a))

/-- 細分による全タプル Čech 項の制限。 -/
def openCoverCechRefinementCochains (P : (Opens X)ᵒᵖ ⥤ ModuleCat R)
    (U : ι → Opens X) (V : κ → Opens X) (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j))
    (k : ℕ) : FullCechCochains (openCoverCechDiagram P U) k →ₗ[R]
      FullCechCochains (openCoverCechDiagram P V) k :=
  LinearMap.pi fun t ↦
    (P.map (homOfLE (cechOpenIntersection_refinement U V ρ hρ t)).op).hom.comp
      (LinearMap.proj (φ := fun s : Fin k → ι ↦
        (openCoverCechDiagram P U).obj (cechTupleSupport s)) (ρ ∘ t))

/-- 細分による制限の成分表示。 -/
theorem openCoverCechRefinementCochains_apply (P : (Opens X)ᵒᵖ ⥤ ModuleCat R)
    (U : ι → Opens X) (V : κ → Opens X) (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j))
    (k : ℕ) (a : FullCechCochains (openCoverCechDiagram P U) k) (t : Fin k → κ) :
    openCoverCechRefinementCochains P U V ρ hρ k a t =
      (P.map (homOfLE (cechOpenIntersection_refinement U V ρ hρ t)).op).hom (a (ρ ∘ t)) := rfl

/-- 細分の制限は余境界と可換。 -/
theorem openCoverCechRefinementCochains_differential
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat R) (U : ι → Opens X) (V : κ → Opens X)
    (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j)) (k : ℕ) :
    (openCoverCechRefinementCochains P U V ρ hρ (k + 1)).comp
        (fullCechDifferential (openCoverCechDiagram P U) k) =
      (fullCechDifferential (openCoverCechDiagram P V) k).comp
        (openCoverCechRefinementCochains P U V ρ hρ k) := by
  apply LinearMap.ext
  intro a
  funext t
  simp only [LinearMap.comp_apply, openCoverCechRefinementCochains_apply,
    fullCechDifferential_apply]
  dsimp only [openCoverCechDiagram]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change (P.map _).hom ((P.map _).hom (a ((ρ ∘ t) ∘ i.succAbove))) =
    (P.map _).hom ((P.map _).hom (a (ρ ∘ (t ∘ i.succAbove))))
  change (P.map _ ≫ P.map _).hom _ = (P.map _ ≫ P.map _).hom _
  rw [← P.map_comp, ← P.map_comp]
  congr 2

/-- 細分による Čech 複体の射。 -/
def openCoverCechRefinementMap (P : (Opens X)ᵒᵖ ⥤ ModuleCat R)
    (U : ι → Opens X) (V : κ → Opens X) (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j)) :
    fullCechComplex (openCoverCechDiagram P U) ⟶
      fullCechComplex (openCoverCechDiagram P V) :=
  CochainComplex.ofHom
    (fun q ↦ ModuleCat.ofHom (openCoverCechRefinementCochains P U V ρ hρ (q + 1))) (by
      intro q
      simp only [fullCechComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      exact (openCoverCechRefinementCochains_differential P U V ρ hρ (q + 1)).symm)

/-- 係数前層の射が有限交叉の係数図式に誘導する射。 -/
def openCoverCechCoefficientMap {P Q : (Opens X)ᵒᵖ ⥤ ModuleCat R}
    (η : P ⟶ Q) (U : ι → Opens X) : openCoverCechDiagram P U ⟶ openCoverCechDiagram Q U where
  app T := η.app (Opposite.op (cechOpenIntersection U T))
  naturality {T S} h := η.naturality _

/-- 細分の制限は係数前層の自然変換に自然。 -/
theorem openCoverCechRefinementCochains_naturality
    {P Q : (Opens X)ᵒᵖ ⥤ ModuleCat R} (η : P ⟶ Q)
    (U : ι → Opens X) (V : κ → Opens X) (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j)) (k : ℕ) :
    (fullCechCochainsMap (openCoverCechCoefficientMap η V) k).comp
        (openCoverCechRefinementCochains P U V ρ hρ k) =
      (openCoverCechRefinementCochains Q U V ρ hρ k).comp
        (fullCechCochainsMap (openCoverCechCoefficientMap η U) k) := by
  apply LinearMap.ext
  intro a
  funext t
  exact (congrArg (fun g ↦ g.hom (a (ρ ∘ t)))
    (η.naturality (homOfLE (cechOpenIntersection_refinement U V ρ hρ t)).op))

/-- 恒等細分は恒等写像を与える。 -/
theorem openCoverCechRefinementCochains_id (P : (Opens X)ᵒᵖ ⥤ ModuleCat R)
    (U : ι → Opens X) (k : ℕ) :
    openCoverCechRefinementCochains P U U id (fun _ ↦ le_rfl) k = LinearMap.id := by
  apply LinearMap.ext
  intro a
  funext t
  change (P.map _).hom (a t) = a t
  have he : (homOfLE (cechOpenIntersection_refinement U U id (fun _ ↦ le_rfl) t)).op =
      𝟙 (Opposite.op (cechOpenIntersection U (cechTupleSupport t))) := Subsingleton.elim _ _
  rw [he, P.map_id]
  rfl

/-- 二つの細分を続けた制限は、合成細分の制限。 -/
theorem openCoverCechRefinementCochains_comp
    {ν : Type} [DecidableEq ν] (P : (Opens X)ᵒᵖ ⥤ ModuleCat R)
    (U : ι → Opens X) (V : κ → Opens X) (W : ν → Opens X)
    (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j))
    (σ : ν → κ) (hσ : ∀ l, W l ≤ V (σ l)) (k : ℕ) :
    (openCoverCechRefinementCochains P V W σ hσ k).comp
        (openCoverCechRefinementCochains P U V ρ hρ k) =
      openCoverCechRefinementCochains P U W (ρ ∘ σ)
        (fun l ↦ (hσ l).trans (hρ (σ l))) k := by
  apply LinearMap.ext
  intro a
  funext t
  change (P.map _ ≫ P.map _).hom (a (ρ ∘ (σ ∘ t))) =
    (P.map _).hom (a ((ρ ∘ σ) ∘ t))
  rw [← P.map_comp]
  congr 2

end SerrePositivity.AlgebraicGeometry
