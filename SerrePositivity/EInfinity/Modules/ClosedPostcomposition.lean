module

public import SerrePositivity.EInfinity.Modules.TensorHomUniversal
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedPostcompositionComponents

/-!
# 元の加群閉零射との dg 合成の全次数成分

概要：M10 の元の実後合成を同じ dg Hom end の作用へ戻す。
方針：既存の一般 dg 閉後合成の全次数式を使う。
規約：HA Construction 1.3.1.6、元の閉射・全整数次数を保持する。
使われ方：同じ cone の最後の切断合成の評価。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：同じ加群閉零射との実 dg 合成は同じ全 Hom 後合成。
方針：既存の一般の全次数成分式を元の加群圏へ適用する。
規約：HA 1.3.1.6、同じ射。使われ方：全 cone の最後の切断項。 -/
lemma modulePostcompose_graded (M : ModuleCategory A D) {P Q : ModuleCategory A D}
    (f : P ⟶ Q) (k : ℤ)
    (v : GradedHom A (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P) k) :
    compose A (closedHomEquiv A (RightModule A D) _ _ f).val v (add_zero k) =
      (eHomWhiskerLeft (Complex A) M f).f k v :=
  (dgClosedPostcomposition_f A (RightModule A D)
    (x := ForgetEnrichment.to (Complex A) M) f k v).symm

end SerrePositivity.EInfinity.Modules
