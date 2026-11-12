module

public import SerrePositivity.KST.Spectra.LoopPositivePower
public import SerrePositivity.KST.Spectra.SphereMappingComponents

/-!
概要：loop 値の球面の写像類と高次ホモトピー群の比較は群同型である。
方針：選んだ loop の積の射の群への作用と球面の代表の後合成の自然性を使う。
規約：SphereSimplex の成分比較の集合の同値の上で積の整合性を実証する。
使われ方：Goerss–Jardine I §7、VIII §1。球面の Hom の次数移動の群としての基礎。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SphereSimplex

def mapClass (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (f : PointedSimplicialSet.sphere.{u} (n + 1) ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right n Y.basepoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (equiv Y (n + 1) f)

lemma mapClass_post {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (n : ℕ)
    (f : PointedSimplicialSet.sphere.{u} (n + 1) ⟶ Y) (p : Y ⟶ Z) :
    pointedGroupMap n p (mapClass Y n f) = mapClass Z n (f ≫ p) := by
  dsimp only [mapClass, pointedGroupMap]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk, equiv_comp]

end SphereSimplex

namespace LoopMappingClasses

lemma groupMap_multiplication (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (PointedObject.prod (PointedObject.basedHom CirclePower.space.{u} Y)
        (PointedObject.basedHom CirclePower.space Y)).right n
      (PointedSimplicialSet.basepoint (PointedObject.prod
        (PointedObject.basedHom CirclePower.space Y)
        (PointedObject.basedHom CirclePower.space Y)))) :
    pointedGroupMap n (multiplication Y) a =
      pointedGroupMap n (PointedObject.prodFst _ _) a *
        pointedGroupMap n (PointedObject.prodSnd _ _) a := by
  let L : PointedSimplicialSet.{u} := PointedObject.basedHom CirclePower.space Y
  have hη : PointedObject.prodLift (PointedObject.prodFst L L)
      (PointedObject.prodSnd L L) = 𝟙 (PointedObject.prod L L) := by
    apply PointedObject.prod_hom_ext <;> simp
  simpa only [hη, Category.id_comp] using
    (groupMap_pair_multiplication (PointedObject.prodFst L L)
      (PointedObject.prodSnd L L) n a)

/-- 概要：loop 値の球面の写像類の積は球面の高次群の積へ移る。
方針：二つの類を射で代表し、積の射の誘導群準同型を二つの射影へ分ける。
規約：n は球面の実際の次元 n+1。
使われ方：Goerss–Jardine I §7。球面の成分比較の群演算の整合性。 -/
lemma sphereComponent_mul (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (a b : LoopMappingClasses (PointedSimplicialSet.sphere.{u} (n + 1)) Y) :
    SphereSimplex.componentClass (PointedObject.basedHom CirclePower.space Y) n (a * b) =
      SphereSimplex.componentClass (PointedObject.basedHom CirclePower.space Y) n a *
        SphereSimplex.componentClass (PointedObject.basedHom CirclePower.space Y) n b := by
  obtain ⟨f, rfl⟩ := classOf_surjective _ Y a
  obtain ⟨g, rfl⟩ := classOf_surjective _ Y b
  rw [← classOf_pair_multiplication]
  simp only [classOf, SphereSimplex.componentClass_familyVertex]
  change SphereSimplex.mapClass _ n (PointedObject.prodLift f g ≫ multiplication Y) =
    SphereSimplex.mapClass _ n f * SphereSimplex.mapClass _ n g
  have h := groupMap_multiplication Y n
    (SphereSimplex.mapClass _ n (PointedObject.prodLift f g))
  simpa only [SphereSimplex.mapClass_post, PointedObject.prodLift_fst,
    PointedObject.prodLift_snd] using h

/-- 概要：loop 値の球面の写像類から loop の高次群への準同型。
方針：成分比較の積の保存から準同型を構成する。
規約：単位の保存は群の準同型の標準構成から従う。
使われ方：Goerss–Jardine I §7。球面の Hom の群の比較。 -/
def sphereComponentHom (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    LoopMappingClasses (PointedSimplicialSet.sphere.{u} (n + 1)) Y →*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom CirclePower.space.{u} Y).right n
        (PointedSimplicialSet.basepoint (PointedObject.basedHom CirclePower.space Y)) :=
  MonoidHom.mk' (SphereSimplex.componentClass (PointedObject.basedHom CirclePower.space Y) n)
    (sphereComponent_mul Y n)

/-- 概要：loop 値の球面の写像類と loop の高次群の標準群同型。
方針：集合としての成分比較の全単射性と積の保存を束ねる。
規約：球面の次元は n+1。
使われ方：Goerss–Jardine I §7、VIII §1。sphere の次数移動の基本段。 -/
def sphereComponentEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    LoopMappingClasses (PointedSimplicialSet.sphere.{u} (n + 1)) Y ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom CirclePower.space.{u} Y).right n
        (PointedSimplicialSet.basepoint (PointedObject.basedHom CirclePower.space Y)) :=
  MulEquiv.ofBijective (sphereComponentHom Y n)
    (SphereSimplex.componentClass_bijective (PointedObject.basedHom CirclePower.space Y) n)

end LoopMappingClasses

end

end SerrePositivity.KST.Spectra
