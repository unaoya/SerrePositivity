module

public import SerrePositivity.KST.Spectra.LoopMappingOperations

/-!
概要：loop のホモトピー類の積を表す実際の点つき射。
方針：二つの射影の類の積の代表を取り、パラメータ制限の群準同型性を使う。
規約：積の厳密な結合性は主張しない。
使われ方：Goerss–Jardine I §7、HA §1.4.2。通常の高次ホモトピー群との積の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.LoopMappingClasses

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：loop の積のホモトピー類を表す実際の点つき射。
方針：直積からの二つの射影の類を掛け、その代表を選ぶ。
規約：選択は実際の射の代表にだけ用いる。
使われ方：Goerss–Jardine I §7、HA §1.4.2。高次群の積の比較。 -/
def multiplication (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    PointedObject.prod (PointedObject.basedHom CirclePower.space.{u} Y)
      (PointedObject.basedHom CirclePower.space Y) ⟶ PointedObject.basedHom CirclePower.space Y :=
  Classical.choose (classOf_surjective _ Y
    (classOf (PointedObject.prodFst _ _) * classOf (PointedObject.prodSnd _ _)))

/-- 概要：選んだ積の射は二つの射影の類の積を表す。
方針：代表を選んだ際の等式を使う。
規約：ホモトピー類の群における等式。
使われ方：Goerss–Jardine I §7。積の射を任意のパラメータへ引き戻す。 -/
theorem classOf_multiplication (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    classOf (multiplication Y) =
      classOf (PointedObject.prodFst _ _) * classOf (PointedObject.prodSnd _ _) :=
  Classical.choose_spec (classOf_surjective _ Y _)

/-- 概要：二つの loop 値の射を積の射で組み合わせると類の積を表す。
方針：代表の等式をパラメータ源の制限準同型で引き戻す。
規約：パラメータ源 A は任意。
使われ方：Goerss–Jardine I §7、HA §1.4.2。積の射の単位則と冪の計算。 -/
theorem classOf_pair_multiplication {A Y : PointedSimplicialSet.{u}} [KanComplex Y.right]
    (f g : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y) :
    classOf (PointedObject.prodLift f g ≫ multiplication Y) = classOf f * classOf g := by
  have h := congrArg (preHom (PointedObject.prodLift f g) Y) (classOf_multiplication Y)
  simpa only [map_mul, preHom_classOf, PointedObject.prodLift_fst,
    PointedObject.prodLift_snd] using h

/-- 概要：積の射の左軸への制限の類は恒等射の類。
方針：組にした射の式で第二成分を零射にする。
規約：等式は点つきホモトピー類で成立する。
使われ方：Goerss–Jardine I §7。積の射の左単位則。 -/
theorem classOf_axisLeft_multiplication (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    classOf (PointedObject.axisLeft _ _ ≫ multiplication Y) = classOf (𝟙 _) := by
  simpa only [PointedObject.axisLeft, classOf_zero, mul_one] using
    classOf_pair_multiplication (Y := Y) (𝟙 (PointedObject.basedHom CirclePower.space Y)) 0

/-- 概要：積の射の右軸への制限の類は恒等射の類。
方針：組にした射の式で第一成分を零射にする。
規約：等式は点つきホモトピー類で成立する。
使われ方：Goerss–Jardine I §7。積の射の右単位則。 -/
theorem classOf_axisRight_multiplication (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    classOf (PointedObject.axisRight _ _ ≫ multiplication Y) = classOf (𝟙 _) := by
  simpa only [PointedObject.axisRight, classOf_zero, one_mul] using
    classOf_pair_multiplication (Y := Y) 0 (𝟙 (PointedObject.basedHom CirclePower.space Y))

end

end SerrePositivity.KST.Spectra.LoopMappingClasses
