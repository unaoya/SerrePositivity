module

public import SerrePositivity.KST.Spectra.SphereMappingHomotopyGroups
public import SerrePositivity.KST.Spectra.CirclePowerPositiveNaturality
public import SerrePositivity.KST.Spectra.LoopMappingTargetNaturality

/-!
概要：球面の Hom の基本群の次数移動の係数に関する自然性。
方針：loop 値の写像類の二つの群の比較と円の群の比較の自然性を合成する。
規約：球面の次元は n+1。
使われ方：Goerss–Jardine I §7、VIII §1。塔の係数の自然な同定の基本段。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma LoopMappingClasses.sphereComponentEquiv_natural {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (p : Y ⟶ Z) (n : ℕ)
    (a : LoopMappingClasses (PointedSimplicialSet.sphere.{u} (n + 1)) Y) :
    sphereComponentEquiv Z n (mapπ₀ (PointedObject.basedHomMap
        (PointedSimplicialSet.sphere.{u} (n + 1))
          (PointedObject.basedHomMap CirclePower.space.{u} (Y := Y) (Z := Z) p)).right a) =
      pointedGroupMap (X := PointedObject.basedHom CirclePower.space Y)
        (Y := PointedObject.basedHom CirclePower.space Z) n
          (PointedObject.basedHomMap CirclePower.space.{u} (Y := Y) (Z := Z) p)
          (sphereComponentEquiv Y n a) :=
  SphereSimplex.componentClass_natural n
    (PointedObject.basedHomMap CirclePower.space.{u} (Y := Y) (Z := Z) p) a

namespace SphereSimplex

lemma fundamentalHomotopyEquiv_formula (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y).right 0
        (PointedSimplicialSet.basepoint
          (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y))) :
    fundamentalHomotopyEquiv Y n a = CirclePower.positiveHomotopyEquiv Y n
      (LoopMappingClasses.sphereComponentEquiv Y n
        ((LoopMappingClasses.groupEquiv (PointedSimplicialSet.sphere.{u} (n + 1)) Y).symm a)) := rfl

/-- 概要：球面の Hom の基本群の次数移動は係数の点つき Kan 射と可換。
方針：写像類の基本群表示、球面の成分比較、円の高次群の三つの自然性を合成する。
規約：球面の次元 n+1、標的の実際の次数 n+2。
使われ方：Goerss–Jardine I §7、VIII §1。正次数の自然性の帰納法の基本段。 -/
theorem fundamentalHomotopyEquiv_natural {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (p : Y ⟶ Z) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y).right 0
        (PointedSimplicialSet.basepoint
          (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y))) :
    fundamentalHomotopyEquiv Z n (pointedGroupMap
        (X := PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y)
        (Y := PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Z) 0
          (PointedObject.basedHomMap (PointedSimplicialSet.sphere.{u} (n + 1))
            (Y := Y) (Z := Z) p) a) =
      pointedGroupMap (n + 1) p (fundamentalHomotopyEquiv Y n a) := by
  let A := PointedSimplicialSet.sphere.{u} (n + 1)
  let b := (LoopMappingClasses.groupEquiv A Y).symm a
  have hb : (LoopMappingClasses.groupEquiv A Z).symm
      (pointedGroupMap (X := PointedObject.basedHom A Y)
        (Y := PointedObject.basedHom A Z) 0 (PointedObject.basedHomMap A (Y := Y) (Z := Z) p) a) =
      mapπ₀ (PointedObject.basedHomMap A
        (PointedObject.basedHomMap CirclePower.space.{u} (Y := Y) (Z := Z) p)).right b := by
    apply (LoopMappingClasses.groupEquiv A Z).injective
    rw [MulEquiv.apply_symm_apply, LoopMappingClasses.groupEquiv_apply,
      LoopMappingClasses.classEquiv_post]
    change _ = pointedGroupMap (X := PointedObject.basedHom A Y)
      (Y := PointedObject.basedHom A Z) 0 (PointedObject.basedHomMap A (Y := Y) (Z := Z) p)
        (LoopMappingClasses.groupEquiv A Y b)
    rw [show LoopMappingClasses.groupEquiv A Y b = a from
      (LoopMappingClasses.groupEquiv A Y).apply_symm_apply a]
  rw [fundamentalHomotopyEquiv_formula, fundamentalHomotopyEquiv_formula, hb,
    LoopMappingClasses.sphereComponentEquiv_natural, CirclePower.positiveHomotopyEquiv_natural]

end SphereSimplex

end

end SerrePositivity.KST.Spectra
