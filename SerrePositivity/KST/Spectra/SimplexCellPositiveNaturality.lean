module

public import SerrePositivity.KST.Spectra.SimplexCellHomotopyGroups
public import SerrePositivity.KST.Spectra.SpherePositiveNaturality

/-!
概要：セルの球面の Hom の正次数群の次数移動の係数自然性。
方針：二つの球面の比較の前合成が標的の後合成と可換であることを使う。
規約：基点は定数射で、正次数群の添字は実際の次数より一つ小さい。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の fiber の係数の比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.SimplexCell

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma positiveHomotopyEquiv_formula (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (n r : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom (sphere.{u} (n + 1)) Y).right r
      (PointedSimplicialSet.basepoint (PointedObject.basedHom (sphere.{u} (n + 1)) Y))) :
    positiveHomotopyEquiv Y n r a = SphereSimplex.positiveHomotopyEquiv Y n r
      (pointedGroupMap
        (X := PointedObject.basedHom (sphere.{u} (n + 1)) Y)
        (Y := PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y) r
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (sphereIso.{u} (n + 1)).inv Y) a) := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  rfl

/-- 概要：セルの球面の次数移動は点つき係数射と可換。
方針：源の同型の前合成の自然性を群へ送り、標準球面の自然性に合成する。
規約：両係数は Kan、球面は n+1 次元。
使われ方：Goerss–Jardine I §7、VIII §1。セルの群の係数自然性。 -/
theorem positiveHomotopyEquiv_natural {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (p : Y ⟶ Z) (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom (sphere.{u} (n + 1)) Y).right r
      (PointedSimplicialSet.basepoint (PointedObject.basedHom (sphere.{u} (n + 1)) Y))) :
    positiveHomotopyEquiv Z n r (pointedGroupMap
      (X := PointedObject.basedHom (sphere.{u} (n + 1)) Y)
      (Y := PointedObject.basedHom (sphere.{u} (n + 1)) Z) r
        (PointedObject.basedHomMap (sphere.{u} (n + 1)) (Y := Y) (Z := Z) p) a) =
      pointedGroupMap (n + 1 + r) p (positiveHomotopyEquiv Y n r a) := by
  have h := (MonoidalClosed.pre (sphereIso.{u} (n + 1)).inv).naturality p
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  change PointedObject.basedHomMap (sphere.{u} (n + 1)) (Y := Y) (Z := Z) p ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (sphereIso.{u} (n + 1)).inv Z =
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (sphereIso.{u} (n + 1)).inv Y ≫
      PointedObject.basedHomMap (PointedSimplicialSet.sphere.{u} (n + 1))
        (Y := Y) (Z := Z) p at h
  have hg := congrArg (fun f ↦ pointedGroupMap r f a) h
  simp only [pointedGroupMap_comp] at hg
  rw [positiveHomotopyEquiv_formula, positiveHomotopyEquiv_formula, hg]
  exact SphereSimplex.positiveHomotopyEquiv_natural p n r _

end

end SerrePositivity.KST.Spectra.SimplexCell
