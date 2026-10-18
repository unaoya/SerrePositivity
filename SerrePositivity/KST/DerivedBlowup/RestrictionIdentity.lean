module

public import SerrePositivity.KST.DerivedBlowup.RestrictionComposition

/-!
概要：KST §3.1 の恒等環射に沿う係数制限を元の dg 圏と比較する。
方針：加群の恒等制限同型を複体へ移し、単位と tensor の式を成分で確認する。
規約：既存の係数制限を変更せず、その標準比較を明示する。
使われ方：係数環が変わるチャート dg 図式の恒等律。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open DifferentialGraded.ScalarExtension
open scoped TensorProduct

variable (A : Type u) [CommRing A]

/-- 概要：恒等環射による係数制限の複体自然同型。
方針：加群の恒等制限同型と複体の恒等関手比較を合成する。
規約：KST §3.1。使われ方：恒等 dg 制限比較の Hom。 -/
def restrictionIdentityIso : restriction (RingHom.id A) ≅ 𝟭 (DifferentialGraded.Complex A) :=
  NatIso.mapHomologicalComplex (ModuleCat.restrictScalarsId A) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (ModuleCat A) (.up ℤ)

/-- 概要：恒等制限比較は tensor の構造射を解消する。
方針：各双次数の純粋 tensor 上で係数制限の構造射を計算する。
規約：KST §3.1。使われ方：恒等 dg 制限比較の乗法条件。 -/
theorem restrictionIdentityIso_tensor (K L : DifferentialGraded.Complex A) :
    Functor.LaxMonoidal.μ (restriction (RingHom.id A)) K L ≫
      (restrictionIdentityIso A).hom.app (K ⊗ L) =
    (restrictionIdentityIso A).hom.app K ⊗ₘ (restrictionIdentityIso A).hom.app L := by
  apply DifferentialGraded.tensorHom_ext
  intro p q n hn
  simp only [comp_f, DifferentialGraded.ι_tensorHom]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (Functor.LaxMonoidal.μ (restriction (RingHom.id A)) K L).f n
    (ιTensorObj ((restriction (RingHom.id A)).obj K)
      ((restriction (RingHom.id A)).obj L) p q n hn (x ⊗ₜ[A] y)) =
    ιTensorObj K L p q n hn (x ⊗ₜ[A] y)
  exact restriction_μ_apply (RingHom.id A) K L p q n hn x y

/-- 概要：恒等制限比較は単位の構造射を解消する。
方針：単位複体の次数0の1で比較し、係数制限の単位公式を使う。
規約：KST §3.1。使われ方：恒等 dg 制限比較の単位条件。 -/
theorem restrictionIdentityIso_unit :
    Functor.LaxMonoidal.ε (restriction (RingHom.id A)) ≫
      (restrictionIdentityIso A).hom.app (𝟙_ (DifferentialGraded.Complex A)) = 𝟙 _ := by
  apply (DifferentialGraded.unitCycleEquiv _).injective
  apply Subtype.ext
  change (Functor.LaxMonoidal.ε (restriction (RingHom.id A))).f 0
    ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) =
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)
  exact restriction_ε_one (RingHom.id A)

/-- 概要：恒等環射による係数制限から元の dg 圏への比較関手。
方針：複体の恒等制限同型の自然性と単位・tensor の比較を使う。
規約：KST §3.1。使われ方：係数付き dg 図式の恒等射。 -/
def restrictionIdentityDGFunctor (D : Type v) [DifferentialGraded.DGCategory A D] :
    DifferentialGraded.DGFunctor A (DGRestriction (RingHom.id A) D) D where
  obj x := x
  map x y := (restrictionIdentityIso A).hom.app (DifferentialGraded.homObject A D x y)
  map_id x := by
    have hn := (restrictionIdentityIso A).hom.naturality
      (eId (DifferentialGraded.Complex A) (C := D) x)
    change (Functor.LaxMonoidal.ε (restriction (RingHom.id A)) ≫
      (restriction (RingHom.id A)).map (eId (DifferentialGraded.Complex A) (C := D) x)) ≫
      _ = eId (DifferentialGraded.Complex A) (C := D) x
    rw [Category.assoc, hn, ← Category.assoc, restrictionIdentityIso_unit, Category.id_comp]
    rfl
  map_comp x y z := by
    have hn := (restrictionIdentityIso A).hom.naturality
      (eComp (DifferentialGraded.Complex A) (C := D) x y z)
    change (Functor.LaxMonoidal.μ (restriction (RingHom.id A)) _ _ ≫
      (restriction (RingHom.id A)).map (eComp (DifferentialGraded.Complex A) (C := D) x y z)) ≫
      _ = ((restrictionIdentityIso A).hom.app (DifferentialGraded.homObject A D x y) ⊗ₘ
        (restrictionIdentityIso A).hom.app (DifferentialGraded.homObject A D y z)) ≫
        eComp (DifferentialGraded.Complex A) (C := D) x y z
    rw [Category.assoc, hn, ← Category.assoc, restrictionIdentityIso_tensor]
    rfl

end SerrePositivity.KST.DerivedBlowup
