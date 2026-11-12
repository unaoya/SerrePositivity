module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryFactor
public import SerrePositivity.KST.Spectra.AnodyneRelativeComparison

/-!
概要：同じホーンを充填する二つの射の、境界定数な欠ける面のホモトピー類の一致。
方針：ホーンを固定するホモトピーを欠ける面へ制限し、その境界の因子分解を使う。
規約：ホーン充填の一意性を仮定しない。面の正次数ホモトピー類を比較する。
使われ方：Goerss–Jardine I §7、VIII §1。零ホモトピーの差の選択独立性。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 同じホーンの二つの充填の欠ける面は、境界を固定してホモトピック。 -/
theorem missingFace_relativeHomotopy {X : SSet.{u}} [KanComplex X]
    {x : X _⦋0⦌} {n : ℕ} (i : Fin (n + 3))
    (s t : X.PtSimplex (n + 1) x) (f g : (Δ[n + 2] : SSet.{u}) ⟶ X)
    (hs : stdSimplex.δ i ≫ f = s.map) (ht : stdSimplex.δ i ≫ g = t.map)
    (hfg : (horn (n + 2) i).ι ≫ f = (horn (n + 2) i).ι ≫ g) :
    Nonempty (s.Homotopy t) := by
  obtain ⟨H, hH⟩ := exists_homotopy_relative_anodyne (horn (n + 2) i).ι
    (anodyneExtensions.horn_ι i) f g hfg
  refine ⟨{
    h := stdSimplex.δ i ▷ (Δ[1] : SSet.{u}) ≫ H.h
    h₀ := by rw [SSet.ι₀_comp_assoc, H.h₀, hs]
    h₁ := by rw [SSet.ι₁_comp_assoc, H.h₁, ht]
    rel := ?_ }⟩
  rw [← s.comm]
  rw [← comp_whiskerRight_assoc, ← _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundaryToHorn_ι, comp_whiskerRight, Category.assoc,
    hH, whiskerRight_fst_assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.boundaryToHorn_ι_assoc, hs]

/-- 同じホーンの二つの充填の境界定数な欠ける面は、同じホモトピー類を表す。 -/
theorem missingFace_class_eq {X : SSet.{u}} [KanComplex X]
    {x : X _⦋0⦌} {n : ℕ} (i : Fin (n + 3))
    (s t : X.PtSimplex (n + 1) x) (f g : (Δ[n + 2] : SSet.{u}) ⟶ X)
    (hs : stdSimplex.δ i ≫ f = s.map) (ht : stdSimplex.δ i ≫ g = t.map)
    (hfg : (horn (n + 2) i).ι ≫ f = (horn (n + 2) i).ι ≫ g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk t := by
  obtain ⟨H⟩ := missingFace_relativeHomotopy i s t f g hs ht hfg
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.eq_of_relativeHomotopy H

end
end SerrePositivity.KST.Spectra
