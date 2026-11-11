module

public import SerrePositivity.KST.Spectra.RelativePathCorner
public import SerrePositivity.KST.Spectra.PointedConnectingRepresentatives

/-!
概要：連結射の全空間側の持ち上げと底の path 側の持ち上げを同時に実現する。
方針：共通の底の単体へ射影する二つの族を相対 path corner に貼り、定数ホーンを充填する。
規約：最後の面以外は定数で固定し、二つの射影を厳密に保つ。
使われ方：Goerss–Jardine I §8。loop と連結射の符号比較の共通持ち上げ。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.RelativePath

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：同じ単体に射影する二つの相対ホーン充填を、一つの path 族に持ち上げる。
方針：二つの族の pullback への射に、corner の Kan fibration 性を適用する。
規約：n=0 も含む。全空間と底の Kan 性は不要。
使われ方：Goerss–Jardine I §8。二方向の連結射の代表を同じ充填から計算する。 -/
theorem common_boundary_lift {E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    [Fibration p.right] (n : ℕ)
    (L : (Δ[n + 1] : SSet.{u}) ⟶ E.right)
    (P : (Δ[n + 1] : SSet.{u}) ⟶ (basedPathSpace B).right)
    (hLP : P ≫ (pathEndpoint B).right = L ≫ p.right)
    (hL : ∀ j, j ≠ Fin.last (n + 1) → stdSimplex.δ j ≫ L = SSet.const E.basepoint)
    (hP : ∀ j, j ≠ Fin.last (n + 1) →
      stdSimplex.δ j ≫ P = SSet.const (basedPathSpace B).basepoint) :
    ∃ T : (Δ[n + 1] : SSet.{u}) ⟶ (basedPathSpace E).right,
      T ≫ (basedPathMap p).right = P ∧ T ≫ (pathEndpoint E).right = L ∧
        ∀ j, j ≠ Fin.last (n + 1) →
          stdSimplex.δ j ≫ T = SSet.const (basedPathSpace E).basepoint := by
  let α (j : Fin (n + 2)) (_ : j ≠ Fin.last (n + 1)) :
      (Δ[n] : SSet.{u}) ⟶ (basedPathSpace E).right :=
    SSet.const (basedPathSpace E).basepoint
  have hα : horn.IsCompatible α := by
    cases n with
    | zero => simp
    | succ n =>
      rw [horn.isCompatible_iff]
      intro _ _ _ _ _
      simp only [α, comp_const]
  let base := pullback.lift P L hLP
  have hp (j : Fin (n + 2)) (hj : j ≠ Fin.last (n + 1)) :
      α j hj ≫ corner p = stdSimplex.δ j ≫ base := by
    apply pullback.hom_ext
    · simp only [α, base, Category.assoc, corner_fst, pullback.lift_fst]
      rw [const_comp, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint, hP j hj]
    · simp only [α, base, Category.assoc, corner_snd, pullback.lift_snd]
      rw [const_comp, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint, hL j hj]
  obtain ⟨T, hT, hbase⟩ := hα.exists_lift (corner p) base hp
  refine ⟨T, ?_, ?_, hT⟩
  · have h := congrArg (fun f ↦ f ≫ pullback.fst _ _) hbase
    simpa only [Category.assoc, corner_fst, base, pullback.lift_fst] using h
  · have h := congrArg (fun f ↦ f ≫ pullback.snd _ _) hbase
    simpa only [Category.assoc, corner_snd, base, pullback.lift_snd] using h

/-- 概要：定数ホーン充填の最後の面は全境界が定数の単体。
方針：各境界面を二面交換でホーンの既知の面へ移す。
規約：零次も含む。底への射影は要求しない。
使われ方：Goerss–Jardine I §8。共通持ち上げの最後の面を群の代表にする。 -/
def lastFaceSimplex {X : SSet.{u}} (e : X _⦋0⦌) (n : ℕ)
    (T : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (hT : ∀ j, j ≠ Fin.last (n + 1) → stdSimplex.δ j ≫ T = SSet.const e) :
    X.PtSimplex n e where
  map := stdSimplex.δ (Fin.last (n + 1)) ≫ T
  comm := by
    obtain _ | n := n
    · ext
    · ext j : 1
      simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
      rw [stdSimplex.δ_comp_δ'_assoc (Fin.castSucc_lt_last j),
        hT _ (Fin.castSucc_ne_last j), comp_const]

/-- 概要：二方向の連結射の最後の面を、一つの path の境界定数単体として得る。
方針：共通の相対ホーン充填の最後の面を取り、二つの射影を計算する。
規約：代表の二射影は元の二つの充填の最後の面そのもの。
使われ方：Goerss–Jardine I §8。loop と連結射の比較ホーンへの入力。 -/
theorem common_boundary_simplex {E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    [Fibration p.right] (n : ℕ)
    (L : (Δ[n + 1] : SSet.{u}) ⟶ E.right)
    (P : (Δ[n + 1] : SSet.{u}) ⟶ (basedPathSpace B).right)
    (hLP : P ≫ (pathEndpoint B).right = L ≫ p.right)
    (hL : ∀ j, j ≠ Fin.last (n + 1) → stdSimplex.δ j ≫ L = SSet.const E.basepoint)
    (hP : ∀ j, j ≠ Fin.last (n + 1) →
      stdSimplex.δ j ≫ P = SSet.const (basedPathSpace B).basepoint) :
    ∃ U : (basedPathSpace E).right.PtSimplex n (basedPathSpace E).basepoint,
      U.map ≫ (basedPathMap p).right = stdSimplex.δ (Fin.last (n + 1)) ≫ P ∧
        U.map ≫ (pathEndpoint E).right = stdSimplex.δ (Fin.last (n + 1)) ≫ L := by
  obtain ⟨T, hproj, hend, hface⟩ := common_boundary_lift p n L P hLP hL hP
  refine ⟨lastFaceSimplex _ n T hface, ?_, ?_⟩
  · change (stdSimplex.δ _ ≫ T) ≫ (basedPathMap p).right = _
    rw [Category.assoc, hproj]
  · change (stdSimplex.δ _ ≫ T) ≫ (pathEndpoint E).right = _
    rw [Category.assoc, hend]

end
end SerrePositivity.KST.Spectra.RelativePath
