module

public import SerrePositivity.KST.Spectra.LoopMappingZeroOrientation
public import SerrePositivity.KST.Spectra.SimplexCellLoopComponents
public import SerrePositivity.KST.Spectra.SkeletalCoefficientNaturality

/-!
概要：セル球面の既存基本群表示と通常の loop 値の成分表示の向き。
方針：円の Kan 置換単位に沿って成分を持ち上げ、既存の基本段の式と逆元比較を合成する。
規約：零 loop 同値で生じる逆元を明示する。
使われ方：Goerss–Jardine I §7–8、VIII §1。骨格の成分係数と群係数の比較。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 円の Kan 置換の正次数比較は、単位への制限と通常の loop 群同型の合成。 -/
lemma CirclePower.positiveHomotopyEquiv_apply (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom space.{u} Y).right n
      (PointedSimplicialSet.basepoint (PointedObject.basedHom space Y))) :
    positiveHomotopyEquiv Y n a = loopPositiveHomotopyEquiv Y n
      (pointedGroupMap n (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed unit Y) a) := by
  dsimp only [positiveHomotopyEquiv, MulEquiv.trans_apply]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism_apply]
  rfl

namespace SimplexCell

/-- セル球面の成分係数は標的の点つき Kan 射に自然。 -/
lemma componentEquiv_natural {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (n : ℕ) (p : Y ⟶ Z)
    (a : π₀ (PointedObject.basedHom (sphere.{u} (n + 1)) Y).right) :
    componentEquiv Z n (mapπ₀ (PointedObject.basedHomMap _ p).right a) =
      pointedGroupMap n p (componentEquiv Y n a) := by
  have hs := PointedMapping.prePointed_post (sphereIso.{u} (n + 1)).inv p
  have hπ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mapPiZero_square _ _
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (sphereIso.{u} (n + 1)).inv Y).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (sphereIso.{u} (n + 1)).inv Z).right
    (congrArg Under.Hom.right hs.symm) a
  change SphereSimplex.componentClass Z n
    (mapπ₀ ((MonoidalClosed.pre (sphereIso.{u} (n + 1)).inv).app Z).right
      (mapπ₀ _ a)) = _
  rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, hπ, SphereSimplex.componentClass_natural]
  change pointedGroupMap n p (SphereSimplex.componentClass Y n
      (mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (sphereIso.{u} (n + 1)).inv Y).right a)) =
    pointedGroupMap n p (SphereSimplex.componentClass Y n
      (mapπ₀ ((MonoidalClosed.pre (sphereIso.{u} (n + 1)).inv).app Y).right a))
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]

/-- 概要：通常の loop の成分をセル球面の基本群表示へ移すと、loop 係数の逆元になる。
方針：置換単位の後合成で成分を持ち上げ、二つの基本段の向きと成分係数の自然性を使う。
規約：同じセル球面と既存の正次数同型を保持する。
使われ方：Goerss–Jardine VIII §1。骨格の係数微分の基本段の逆符号。 -/
theorem positiveHomotopyEquiv_loopZero (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ)
    (a : π₀ (PointedObject.basedHom (sphere.{u} (n + 1)) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right) :
    positiveHomotopyEquiv Y n 0
        (PointedMapping.loopZeroComponentEquiv (sphere.{u} (n + 1)) Y a) =
      (loopPositiveHomotopyEquiv Y n (componentEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n a))⁻¹ := by
  obtain ⟨c, rfl⟩ := (PointedMapping.loopUnit_post_piZero_bijective (sphere.{u} (n + 1)) Y).2 a
  rw [PointedMapping.loopZeroComponentEquiv_unit, map_inv]
  have hz := positiveHomotopyEquiv_zero_loopClasses Y n c
  rw [LoopMappingClasses.groupEquiv_apply] at hz
  rw [hz, componentEquiv_natural, CirclePower.positiveHomotopyEquiv_apply]

end SimplexCell
end
end SerrePositivity.KST.Spectra
