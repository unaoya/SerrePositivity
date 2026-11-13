module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCechEvaluation
public import SerrePositivity.AlgebraicGeometry.CechTupleRefinementSupport

/-!
概要：細分の二つの添字の選択を、制限付き整数鎖の評価で比較する。
方針：整数鎖の比較ホモトピーの頂点集合を制御し、各交叉上で評価する。
規約：二つの選択は同じ細分被覆の上で与える。
使われ方：共通アフィン細分の Čech H の比較が選択に依存しないこと。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace
universe u v w
variable {X : Type u} [TopologicalSpace X] {R : Type w} [CommRing R]
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R) (U : ι → Opens X) (V : κ → Opens X)
variable (ρ σ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j)) (hσ : ∀ j, V j ≤ U (σ j))

include hρ hσ in
/-- 細分の交叉は、二つの添字の像を合わせた交叉に含まれる。 -/
theorem cechOpenIntersection_refinement_union (T : Finset κ) :
    cechOpenIntersection V T ≤ cechOpenIntersection U (T.image ρ ∪ T.image σ) := by
  apply le_iInf
  intro i
  apply le_iInf
  intro hi
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact (iInf_le_of_le j (iInf_le_of_le hj le_rfl)).trans (hρ j)
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact (iInf_le_of_le j (iInf_le_of_le hj le_rfl)).trans (hσ j)

include hρ hσ in
/-- 比較ホモトピーに現れるタプルの交叉は、細分の交叉を含む。 -/
theorem openCoverCechRefinementHomotopy_support {k : ℕ} (t : Fin k → κ)
    (s : Fin (k + 1) → ι)
    (hs : s ∈ (cechTupleRefinementHomotopy ρ σ k (Finsupp.single t 1)).support) :
    cechOpenIntersection V (cechTupleSupport t) ≤
      cechOpenIntersection U (cechTupleSupport s) :=
  (cechOpenIntersection_refinement_union U V ρ σ hρ hσ _).trans
    (cechOpenIntersection_antitone U (cechTupleRefinementHomotopy_support ρ σ t s hs))

/-- 細分の二つの選択を比較する Čech の次数一低い成分。 -/
def openCoverCechRefinementHomotopyTerm (k : ℕ) :
    FullCechCochains (openCoverCechDiagram P U) (k + 1) →ₗ[R]
      FullCechCochains (openCoverCechDiagram P V) k :=
  LinearMap.pi fun t ↦ openCoverCechEvaluateAt P U
    (cechOpenIntersection V (cechTupleSupport t)) (k + 1)
    (cechTupleRefinementHomotopy ρ σ k (Finsupp.single t 1))

/-- 長さ零での比較成分は零。 -/
theorem openCoverCechRefinementHomotopyTerm_zero :
    openCoverCechRefinementHomotopyTerm P U V ρ σ 0 = 0 := by
  apply LinearMap.ext
  intro a
  funext t
  simp [openCoverCechRefinementHomotopyTerm, cechTupleRefinementHomotopy,
    cechTupleComparisonHomotopy, LinearMap.comp_apply, LinearMap.zero_apply]
  all_goals rfl

include hρ hσ in
/-- 比較鎖の境界への評価は、比較コチェインの余境界に対応する。 -/
theorem openCoverCechRefinementHomotopyTerm_boundary (k : ℕ) (t : Fin (k + 1) → κ)
    (a : FullCechCochains (openCoverCechDiagram P U) (k + 1)) :
    openCoverCechEvaluateAt P U (cechOpenIntersection V (cechTupleSupport t)) (k + 1)
      (cechTupleRefinementHomotopy ρ σ k (cechTupleBoundary k (Finsupp.single t 1))) a =
    fullCechDifferential (openCoverCechDiagram P V) k
      (openCoverCechRefinementHomotopyTerm P U V ρ σ k a) t := by
  simp only [cechTupleBoundary, Finsupp.linearCombination_single, one_smul,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [fullCechDifferential_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change openCoverCechEvaluateAt P U (cechOpenIntersection V (cechTupleSupport t)) (k + 1)
      (cechTupleRefinementHomotopy ρ σ k (Finsupp.single (t ∘ i.succAbove) 1)) a =
    (P.map (homOfLE (cechOpenIntersection_antitone V
      (cechTupleSupport_face_subset t i))).op).hom
      (openCoverCechEvaluateAt P U (cechOpenIntersection V
        (cechTupleSupport (t ∘ i.succAbove))) (k + 1)
        (cechTupleRefinementHomotopy ρ σ k (Finsupp.single (t ∘ i.succAbove) 1)) a)
  exact (openCoverCechEvaluateAt_restrict P U
    (cechOpenIntersection_antitone V (cechTupleSupport_face_subset t i)) _
    (openCoverCechRefinementHomotopy_support U V ρ σ hρ hσ (t ∘ i.succAbove)) a).symm

/-- 二つの細分写像は、制限付きの比較成分によるコチェインホモトピーで結ばれる。 -/
theorem openCoverCechRefinementHomotopyTerm_identity (k : ℕ) :
    (openCoverCechRefinementHomotopyTerm P U V ρ σ (k + 1)).comp
        (fullCechDifferential (openCoverCechDiagram P U) (k + 1)) +
      (fullCechDifferential (openCoverCechDiagram P V) k).comp
        (openCoverCechRefinementHomotopyTerm P U V ρ σ k) =
    openCoverCechRefinementCochains P U V σ hσ (k + 1) -
      openCoverCechRefinementCochains P U V ρ hρ (k + 1) := by
  apply LinearMap.ext
  intro a
  funext t
  have hh := congrArg (fun z ↦ openCoverCechEvaluateAt P U
    (cechOpenIntersection V (cechTupleSupport t)) (k + 1) z a)
    (LinearMap.congr_fun (cechTupleRefinementHomotopy_identity ρ σ k) (Finsupp.single t 1))
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    map_add, map_sub, cechTupleReindex_single] at hh
  rw [openCoverCechEvaluateAt_boundary P U (k + 1) _
      (openCoverCechRefinementHomotopy_support U V ρ σ hρ hσ t) a,
    openCoverCechRefinementHomotopyTerm_boundary P U V ρ σ hρ hσ k t a,
    openCoverCechEvaluateAt_single P U (cechOpenIntersection_refinement U V σ hσ t),
    openCoverCechEvaluateAt_single P U (cechOpenIntersection_refinement U V ρ hρ t)] at hh
  exact hh

end SerrePositivity.AlgebraicGeometry
