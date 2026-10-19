module

public import SerrePositivity.KST.Spectra.PointedTowerRepresentatives
public import SerrePositivity.KST.Spectra.FibrationTower

/-!
概要：Kan fibration の塔の極限のホモトピー群から段ごとの整合する類への比較。
方針：厳密に整合する単体を明示的な極限へ組み立て、各射影で代表を回収する。
規約：正次数の比較の全射性。単射性や lim¹ の消滅は仮定しない。
使われ方：Goerss–Jardine VIII §1。Milnor 完全列と塔の収束の準備。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.PointedFibrationTower

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)

/-- 塔の基点の整合族が与える極限の実際の基点。 -/
def limitBasepoint : (FibrationTower.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right)) _⦋0⦌ :=
  ⟨fun n ↦ (X n).basepoint, fun n ↦ OmegaSpectrum.pointedMap_basepoint (p n)⟩

/-- 整合族の基点を各段へ射影すると、その段の基点。 -/
@[simp]
lemma projection_limitBasepoint (n : ℕ) :
    (FibrationTower.projection (fun n ↦ (X n).right) (fun n ↦ (p n).right) n).app _
      (limitBasepoint X p) = (X n).basepoint := rfl

/-- 厳密に整合する境界定数単体の族を極限の境界定数単体へまとめる。 -/
def limitSimplex (r : ℕ)
    (s : ∀ n, (X n).right.PtSimplex (r + 1) (X n).basepoint)
    (hs : ∀ n, mapSimplex (p n).right (OmegaSpectrum.pointedMap_basepoint (p n))
      (s (n + 1)) = s n) :
    (FibrationTower.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right)).PtSimplex
      (r + 1) (limitBasepoint X p) where
  map := FibrationTower.lift _ _ (fun n ↦ (s n).map)
    (fun n ↦ congrArg RelativeMorphism.map (hs n))
  comm := by
    apply FibrationTower.hom_ext (fun n ↦ (X n).right) (fun n ↦ (p n).right)
    intro n
    simpa only [Category.assoc, FibrationTower.lift_projection, Subcomplex.ofSimplex_ι,
      comp_const, const_comp, projection_limitBasepoint] using (s n).comm

/-- 極限へ組み立てた単体の各射影は、指定した代表そのもの。 -/
lemma limitSimplex_projection (r : ℕ)
    (s : ∀ n, (X n).right.PtSimplex (r + 1) (X n).basepoint)
    (hs : ∀ n, mapSimplex (p n).right (OmegaSpectrum.pointedMap_basepoint (p n))
      (s (n + 1)) = s n) (n : ℕ) :
    mapSimplex (FibrationTower.projection (fun n ↦ (X n).right) (fun n ↦ (p n).right) n) rfl
      (limitSimplex X p r s hs) = s n := by
  apply RelativeMorphism.ext
  exact FibrationTower.lift_projection _ _ (fun n ↦ (s n).map)
    (fun n ↦ congrArg RelativeMorphism.map (hs n)) n

variable [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right]

/-- 極限の正次数ホモトピー群から各段の群への標準射影。 -/
def limitGroupProjection (r n : ℕ) :
    KanHomotopyGroup (FibrationTower.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right))
        r (limitBasepoint X p) →*
      KanHomotopyGroup (X n).right r (X n).basepoint :=
  KanHomotopyGroup.map
    (FibrationTower.projection (fun n ↦ (X n).right) (fun n ↦ (p n).right) n) rfl

/-- 整合する正次数ホモトピー類の族は、極限のホモトピー類の射影として得られる。 -/
theorem exists_limit_class (r : ℕ)
    (a : ∀ n, KanHomotopyGroup (X n).right r (X n).basepoint)
    (ha : ∀ n, pointedGroupMap r (p n) (a (n + 1)) = a n) :
    ∃ b : KanHomotopyGroup
      (FibrationTower.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right)) r (limitBasepoint X p),
      ∀ n, limitGroupProjection X p r n b = a n := by
  obtain ⟨s, hs, hcomp⟩ := exists_compatible_representatives X p r a ha
  refine ⟨KanHomotopyGroup.mk (limitSimplex X p r s hcomp), ?_⟩
  intro n
  change KanHomotopyGroup.map _ rfl (KanHomotopyGroup.mk _) = _
  rw [KanHomotopyGroup.map_mk, limitSimplex_projection]
  exact hs n

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
