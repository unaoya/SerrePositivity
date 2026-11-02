module

public import SerrePositivity.KST.DerivedBlowup.RepresentableUnitNaturality
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction

/-!
概要：KST §3.1 の regular 比較に使う閉零 Yoneda 射の回収公式。
方針：代表加群の単位を Yoneda 拡張すると恒等射であることを作用で確認する。
規約：通常圏の射にも全次数自然性を保つ。
使われ方：重み付けされた regular 自己同型との合成を局所生成元へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory Opposite DifferentialGraded

variable (R : Type u) [CommRing R] {D : Type v} [DGCategory R D] [Small.{u} D]

/-- 概要：代表加群の単位の指定 Yoneda 拡張は恒等射。
方針：各斉次成分で代表加群の作用を計算し、右単位律を使う。
規約：KST §3.1。使われ方：代表加群を始域に持つ射の生成元による回収。 -/
theorem representableUnitMap_identity (x : D) :
    representableUnitMap R x (representable R x) (eId (Complex R) x) =
      𝟙 (ForgetEnrichment.of (Complex R) (representable R x)) := by
  apply moduleMorphism_ext
  intro y
  rw [CategoryTheory.Functor.map_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((moduleEvaluation R D y).map
    (representableUnitMap R x (representable R x) (eId (Complex R) x))).f q) z = z
  rw [representableUnitMap_apply, representable_action]
  exact unit_forward R z

/-- 概要：代表加群からの射は単位生成元の像を Yoneda 拡張して回収できる。
方針：恒等 Yoneda 射に後合成自然性を適用する。
規約：KST §3.1。使われ方：regular 自己同型と局所比較の合成を計算する。 -/
theorem representableUnitMap_recover (x : D) {M : ModuleCategory R D}
    (f : ForgetEnrichment.of (Complex R) (representable R x) ⟶ M) :
    representableUnitMap R x (ForgetEnrichment.to (Complex R) M)
        (eId (Complex R) x ≫ (moduleEvaluation R D x).map f) = f := by
  have he := representableUnitMap_postcomp R x
    (M := ForgetEnrichment.of (Complex R) (representable R x)) (eId (Complex R) x) f
  change representableUnitMap R x (representable R x) (eId (Complex R) x) ≫ f = _ at he
  rw [representableUnitMap_identity, Category.id_comp] at he
  exact he.symm

end SerrePositivity.KST.DerivedBlowup
