module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionEvaluationFiniteSupportColimit
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Data.Finset.Prod

/-! # 有限部分根族の有界δ深さによる実評価図式 -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {σ : Type u}

/-- 有限座標集合を、その根と最大δ深さによる全長方形へ広げる。 -/
def deltaDivisionCoordinateHull (S : Finset (σ × ℕ)) : Finset (σ × ℕ) := by
  classical
  exact (S.image Prod.fst) ×ˢ Finset.range (S.sup Prod.snd + 1)

/-- 標準長方形は、選ばれた根の最大深さ以下の座標をちょうど含む。 -/
theorem mem_deltaDivisionCoordinateHull (S : Finset (σ × ℕ)) (z : σ × ℕ) :
    letI : DecidableEq σ := Classical.decEq σ
    z ∈ deltaDivisionCoordinateHull S ↔ z.1 ∈ S.image Prod.fst ∧ z.2 ≤ S.sup Prod.snd := by
  classical
  simp only [deltaDivisionCoordinateHull, Finset.mem_product, Finset.mem_range,
    Nat.lt_succ_iff]

/-- 元のすべての有限座標は、その標準長方形に含まれる。 -/
theorem subset_deltaDivisionCoordinateHull (S : Finset (σ × ℕ)) :
    S ⊆ deltaDivisionCoordinateHull S := by
  classical
  intro z hz
  exact (mem_deltaDivisionCoordinateHull S z).mpr
    ⟨Finset.mem_image.mpr ⟨z, hz, rfl⟩, Finset.le_sup hz⟩

/-- 有限座標集合の包含は、標準長方形の包含を与える。 -/
theorem deltaDivisionCoordinateHull_mono :
    Monotone (deltaDivisionCoordinateHull (σ := σ)) := by
  classical
  intro S T h z hz
  obtain ⟨hs, hn⟩ := (mem_deltaDivisionCoordinateHull S z).mp hz
  exact (mem_deltaDivisionCoordinateHull T z).mpr
    ⟨Finset.image_mono Prod.fst h hs, hn.trans (Finset.sup_mono h)⟩

/-- 有限座標添字上の、標準長方形へ広げる関手。 -/
def deltaDivisionCoordinateHullFunctor : Finset (σ × ℕ) ⥤ Finset (σ × ℕ) :=
  deltaDivisionCoordinateHull_mono.functor

/-- この標準長方形関手は余終であり、評価環を尽くす余極限を変えない。 -/
theorem deltaDivisionCoordinateHullFunctor_final :
    Functor.Final (deltaDivisionCoordinateHullFunctor (σ := σ)) := by
  classical
  apply Functor.final_of_exists_of_isFiltered
  · intro S
    exact ⟨S, ⟨homOfLE (subset_deltaDivisionCoordinateHull S)⟩⟩
  · intro S T f g
    exact ⟨T, 𝟙 T, Subsingleton.elim _ _⟩

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A) (a : σ → A)
local notation "L" => RelativeFreeDeltaRing (R := A) σ
local notation "H" => deltaDivisionCoordinateHullFunctor (σ := σ)
local notation "F" => deltaDivisionFiniteSupportModuleDiagram D a

/-- 有限部分根族・全有限δ深さの商のみからなる、元の実図式の前合成。 -/
def deltaDivisionBoundedSupportModuleDiagram : Finset (σ × ℕ) ⥤ ModuleCat.{u} L := H ⋙ F

/-- 同じβ作用の評価環を頂点に持つ、有界深さ有限部分族の標準余錐。 -/
def deltaDivisionBoundedSupportEvalCocone :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    Cocone (deltaDivisionBoundedSupportModuleDiagram D a) := by
  letI := deltaDivisionSourceEvaluationAlgebra D a
  exact (deltaDivisionFiniteSupportEvalCocone D a).whisker H

/-- 評価環は、Tor消滅を扱う有界深さ有限部分族の商図式の実余極限である。 -/
def deltaDivisionBoundedSupportEvalIsColimit :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    IsColimit (deltaDivisionBoundedSupportEvalCocone D a) := by
  letI := deltaDivisionSourceEvaluationAlgebra D a
  letI := deltaDivisionCoordinateHullFunctor_final (σ := σ)
  exact (Functor.Final.isColimitWhiskerEquiv H _).symm
    (deltaDivisionFiniteSupportEvalIsColimit D a)

/-- 有界深さ有限部分族図式の実圏論的余極限と、元のβ評価環との標準同型。 -/
def deltaDivisionBoundedSupportColimitEvalIso :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    colimit (deltaDivisionBoundedSupportModuleDiagram D a) ≅ ModuleCat.of L A := by
  letI := deltaDivisionSourceEvaluationAlgebra D a
  exact (colimit.isColimit _).coconePointUniqueUpToIso
    (deltaDivisionBoundedSupportEvalIsColimit D a)

/-- 標準余極限同型は、全段の元のβ評価射を保つ。 -/
theorem deltaDivisionBoundedSupportColimitEvalIso_ι (S : Finset (σ × ℕ)) :
    letI := deltaDivisionSourceEvaluationAlgebra D a
    colimit.ι (deltaDivisionBoundedSupportModuleDiagram D a) S ≫
      (deltaDivisionBoundedSupportColimitEvalIso D a).hom =
        ModuleCat.ofHom (deltaDivisionFiniteSupportEval D a (deltaDivisionCoordinateHull S)) := by
  let := deltaDivisionSourceEvaluationAlgebra D a
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (deltaDivisionBoundedSupportEvalIsColimit D a) S

end SerrePositivity.BhattScholze
