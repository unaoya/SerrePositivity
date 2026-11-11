module

public import SerrePositivity.KST.Spectra.SphereFundamentalNaturality
public import SerrePositivity.KST.Spectra.SphereMappingHomotopyFormula

/-!
概要：球面の Hom の正次数の次数移動の係数に関する自然性。
方針：loop の群の自然性と内部 Hom の交換の可換式を帰納的に合成する。
規約：実際の係数の射から誘導される通常の群準同型を比較する。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の fiber の係数の自然な同定。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SphereSimplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma loopSwap_natural {Y Z : PointedSimplicialSet.{u}} (p : Y ⟶ Z) (n : ℕ) :
    PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
        (Y := PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y)
        (Z := PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Z)
        (PointedObject.basedHomMap (PointedSimplicialSet.sphere.{u} (n + 1))
          (Y := Y) (Z := Z) p) ≫ (loopSwap Z n).hom =
      (loopSwap Y n).hom ≫ PointedObject.basedHomMap
        (PointedSimplicialSet.sphere.{u} (n + 1)) (Y := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (Z := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z)
          (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (Y := Y) (Z := Z) p) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.natural_post
    (C := PointedSimplicialSet.{u}) PointedSimplicialSet.circle.{u}
      (PointedSimplicialSet.sphere.{u} (n + 1)) p

/-- 概要：球面の Hom の全正次数群の次数移動は係数射に自然。
方針：基本群の自然性から帰納し、loop の群の逆同型と源の交換の自然性を使う。
規約：球面の次元 n+1、Hom の次数 r+1、標的の次数 n+r+2。
使われ方：Goerss–Jardine I §7、VIII §1。塔の係数射の群での計算。 -/
theorem positiveHomotopyEquiv_natural {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (p : Y ⟶ Z) (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y).right r
      (PointedSimplicialSet.basepoint
        (PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y))) :
    positiveHomotopyEquiv Z n r (pointedGroupMap
        (X := PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Y)
        (Y := PointedObject.basedHom (PointedSimplicialSet.sphere.{u} (n + 1)) Z) r
          (PointedObject.basedHomMap (PointedSimplicialSet.sphere.{u} (n + 1))
            (Y := Y) (Z := Z) p) a) =
      pointedGroupMap (n + 1 + r) p (positiveHomotopyEquiv Y n r a) := by
  induction r generalizing Y Z with
  | zero => exact fundamentalHomotopyEquiv_natural p n a
  | succ r ih =>
    let A := PointedSimplicialSet.sphere.{u} (n + 1)
    let HY : PointedSimplicialSet.{u} := PointedObject.basedHom A Y
    let HZ : PointedSimplicialSet.{u} := PointedObject.basedHom A Z
    let mp : HY ⟶ HZ := PointedObject.basedHomMap A (Y := Y) (Z := Z) p
    let lp : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z :=
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (Y := Y) (Z := Z) p
    let lmp : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace HY ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace HZ :=
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (Y := HY) (Z := HZ) mp
    let mlp : PointedObject.basedHom A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) ⟶
        PointedObject.basedHom A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z) :=
      PointedObject.basedHomMap A (Y := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (Z := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z) lp
    let b := (loopPositiveHomotopyEquiv HY r).symm a
    have hb : (loopPositiveHomotopyEquiv HZ r).symm
        (pointedGroupMap (X := HY) (Y := HZ) (r + 1) mp a) =
        pointedGroupMap (X := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace HY) (Y := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace HZ) r lmp b := by
      apply (loopPositiveHomotopyEquiv HZ r).injective
      rw [MulEquiv.apply_symm_apply, loopPositiveHomotopyEquiv_natural]
      rw [show loopPositiveHomotopyEquiv HY r b = a from
        (loopPositiveHomotopyEquiv HY r).apply_symm_apply a]
    have hs : lmp ≫ (loopSwap Z n).hom = (loopSwap Y n).hom ≫ mlp :=
      loopSwap_natural p n
    have hg := congrArg (fun f : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace HY ⟶ PointedObject.basedHom A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z) ↦
      pointedGroupMap (X := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace HY)
        (Y := PointedObject.basedHom A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z)) r f b) hs
    simp only [pointedGroupMap_comp] at hg
    rw [positiveHomotopyEquiv_succ, positiveHomotopyEquiv_succ, hb, hg, ih lp]
    exact loopPositiveHomotopyEquiv_natural p (n + 1 + r) _

end

end SerrePositivity.KST.Spectra.SphereSimplex
