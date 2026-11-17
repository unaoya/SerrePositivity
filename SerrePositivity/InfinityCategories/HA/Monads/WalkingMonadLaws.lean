module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingMonad
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
概要：walking monad の順序和の全単位・結合則。
方針：有限順序集合の結合子・単位子が等式による輸送であることから、列の関手の等式を示す。
規約：全ての次数で証明し、nerve の辺だけの等式にはしない。
使われ方：HA §4.7.2–§4.7.3、Proposition 4.7.3.3 の全モナドの添字の合成。
Riehl–Verity Remark 3.3.8 の順序和、Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

universe u v w
open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：順序和の対象の結合則。
方針：空順序集合の場合を分け、残りを自然数の加法の結合則に帰着する。
規約：有限順序集合の等式。使われ方：HA §4.7.2 の walking monad の合成。 -/
lemma ordinalSum_assoc (x y z : AugmentedSimplexCategory) :
    (x ⊗ y) ⊗ z = x ⊗ (y ⊗ z) := by
  change AugmentedSimplexCategory.tensorObj (AugmentedSimplexCategory.tensorObj x y) z =
    AugmentedSimplexCategory.tensorObj x (AugmentedSimplexCategory.tensorObj y z)
  cases x <;> cases y <;> cases z <;>
    simp only [AugmentedSimplexCategory.tensorObj, AugmentedSimplexCategory.tensorObjOf]
  congr 2; omega

/-- 概要：順序和の結合子は同じ対象等式の輸送。
方針：結合子の既存の構成を場合分けする。規約：任意の三つの有限順序集合。
使われ方：HA §4.7.2 の全結合則を関手の等式に移す。 -/
lemma ordinalSum_associator_hom (x y z : AugmentedSimplexCategory) :
    (α_ x y z).hom = eqToHom (ordinalSum_assoc x y z) := by
  cases x <;> cases y <;> cases z <;> rfl

variable {I : Type v} [Category.{w} I]

/-- 概要：順序和の列の合成は関手そのものとして結合的。
方針：結合子の自然同型が対象等式の輸送であることを使う。
規約：Iの任意の射上で比較する。使われ方：HA §4.7.2 の全単体の結合則。 -/
lemma ordinalSumFunctor_assoc (F G H : I ⥤ AugmentedSimplexCategory) :
    ((F.prod' G ⋙ tensor _).prod' H ⋙ tensor _) =
      (F.prod' (G.prod' H ⋙ tensor _) ⋙ tensor _) := by
  let e : ((F.prod' G ⋙ tensor _).prod' H ⋙ tensor _) ≅
      (F.prod' (G.prod' H ⋙ tensor _) ⋙ tensor _) :=
    NatIso.ofComponents (fun i => α_ (F.obj i) (G.obj i) (H.obj i))
      (fun f => associator_naturality (F.map f) (G.map f) (H.map f))
  exact Functor.ext_of_iso e
    (fun i => ordinalSum_assoc (F.obj i) (G.obj i) (H.obj i))
    (fun i => ordinalSum_associator_hom _ _ _)

/-- 概要：空順序集合と値の順序和は元の値。
方針：空の場合を含む既存の順序和を場合分けする。規約：左単位の対象等式。
使われ方：HA §4.7.2 の単位付き合成。 -/
lemma ordinalSum_leftUnit (x : AugmentedSimplexCategory) :
    (WithInitial.star : AugmentedSimplexCategory) ⊗ x = x := by
  cases x <;> rfl

/-- 概要：値と空順序集合の順序和は元の値。
方針：既存の順序和を場合分けする。規約：右単位の対象等式。
使われ方：HA §4.7.2 の単位付き合成。 -/
lemma ordinalSum_rightUnit (x : AugmentedSimplexCategory) :
    x ⊗ (WithInitial.star : AugmentedSimplexCategory) = x := by
  cases x <;> rfl

/-- 概要：順序和の左単位子は対象等式による輸送。
方針：空か非空かで場合分けする。規約：全ての有限順序集合。
使われ方：HA §4.7.2 の全左単位則。 -/
lemma ordinalSum_leftUnitor_hom (x : AugmentedSimplexCategory) :
    (λ_ x).hom = eqToHom (ordinalSum_leftUnit x) := by
  cases x <;> rfl

/-- 概要：順序和の右単位子は対象等式による輸送。
方針：有限順序集合を場合分けする。規約：同じ右単位の等式。
使われ方：HA §4.7.2 の全右単位則。 -/
lemma ordinalSum_rightUnitor_hom (x : AugmentedSimplexCategory) :
    (ρ_ x).hom = eqToHom (ordinalSum_rightUnit x) := by
  cases x <;> rfl

/-- 概要：空順序集合の定値列を左に合成しても関手は変わらない。
方針：左単位子の自然同型と等式による輸送を比較する。
規約：全てのIの射での関手の等式。使われ方：HA §4.7.2 の全左単位則。 -/
lemma ordinalSumFunctor_leftUnit (F : I ⥤ AugmentedSimplexCategory) :
    (((Functor.const I).obj WithInitial.star).prod' F ⋙ tensor _) = F := by
  let e : (((Functor.const I).obj WithInitial.star).prod' F ⋙ tensor _) ≅ F :=
    NatIso.ofComponents (fun i => λ_ (F.obj i))
      (fun f => leftUnitor_naturality (F.map f))
  exact Functor.ext_of_iso e (fun i => ordinalSum_leftUnit (F.obj i))
    (fun i => ordinalSum_leftUnitor_hom (F.obj i))

/-- 概要：空順序集合の定値列を右に合成しても関手は変わらない。
方針：右単位子が対象等式の輸送であることを使う。
規約：全次数の単位則。使われ方：HA §4.7.2 の全右単位則。 -/
lemma ordinalSumFunctor_rightUnit (F : I ⥤ AugmentedSimplexCategory) :
    (F.prod' ((Functor.const I).obj WithInitial.star) ⋙ tensor _) = F := by
  let e : (F.prod' ((Functor.const I).obj WithInitial.star) ⋙ tensor _) ≅ F :=
    NatIso.ofComponents (fun i => ρ_ (F.obj i))
      (fun f => rightUnitor_naturality (F.map f))
  exact Functor.ext_of_iso e (fun i => ordinalSum_rightUnit (F.obj i))
    (fun i => ordinalSum_rightUnitor_hom (F.obj i))

/-- 概要：walking monad の順序和の単体写像は実際の内部モノイドをなす。
方針：各次数の有限順序集合の列の単位・結合則で構成する。
規約：未証明のinstanceを仮定しない。使われ方：HA §4.7.2–§4.7.3。 -/
@[instance_reducible]
def walkingMonadMonObj : MonObj WalkingMonadShape.{u} where
  one := walkingMonadUnit
  mul := walkingMonadComposition
  one_mul := by
    ext n p
    apply ULift.ext
    exact ordinalSumFunctor_leftUnit p.2.down
  mul_one := by
    ext n p
    apply ULift.ext
    exact ordinalSumFunctor_rightUnit p.1.down
  mul_assoc := by
    ext n p
    apply ULift.ext
    exact ordinalSumFunctor_assoc p.1.1.down p.1.2.down p.2.down

end SerrePositivity.InfinityCategories.HA.Monads
