module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleCofiberFiberContraction

/-! # cofiber と fiber の比較の合成の実原始元

概要：逆射の後の比較と恒等の差を全 Hom end の境界として表す。
方針：fiber の逆座標へ (−snd⋅h,0) を入れ、行列微分と分解式を使う。
規約：次数 −1 の明示成分。使われ方：β3 の比較辺の ∞ 同値性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 比較のもう一方の合成の差を解く次数 −1 成分。 -/
def dgModuleCofiberFiberHomotopyElement (f : M ⟶ N) :
    GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f)) (-1) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D
    (ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f)))
    (moduleConeInr A D f) (-2)).symm (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberContractionN A D f, 0)

/-- 原始元の微分の二つの実座標。 -/
lemma dgModuleCofiberFiberHomotopyElement_differential_coordinates (f : M ⟶ N) :
    (moduleHom A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))).d (-1) 0
        (dgModuleCofiberFiberHomotopyElement A D f) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D
        (ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f)))
        (_root_.SerrePositivity.DifferentialGraded.moduleConeInr A D f) (-1)).symm
        (_root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) f)).val
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberRetractElement A D f) (zero_add 0) -
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjectionElement A D (moduleConeInr A D f),
         -compose A (moduleConeInrElement A D f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberContractionN A D f)
          (add_zero (-1))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates_symm_differential A D
    (T := ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f)))
    (moduleConeInr A D f) (-2) (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberContractionN A D f) 0
  have hneg : (moduleHom A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)).d (-1) 0
      (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberContractionN A D f) =
      -(moduleHom A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)).d (-1) 0
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberContractionN A D f) := map_neg _ _
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right (A := A) (moduleConeInrElement A D f)
    (0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N) (-1))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberContractionN A D f) (add_zero (-1))
  simp only [zero_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero] at hc
  change (moduleHom A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))).d (-1) 0
      (dgModuleCofiberFiberHomotopyElement A D f) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberHomCoordinates A D
      (ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f)))
      (_root_.SerrePositivity.DifferentialGraded.moduleConeInr A D f) (-1)).symm
      ((moduleHom A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)).d (-1) 0
          (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberContractionN A D f),
       compose A (moduleConeInrElement A D f) (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberContractionN A D f)
         (add_zero (-1)) -
       (moduleHom A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D (moduleConeInr A D f))
         (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f))).d (-2) (-1) 0) at h
  rw [hneg, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberContractionN_differential, hc, map_zero, sub_zero] at h
  rw [h]
  congr 2
  abel

end SerrePositivity.InfinityCategories.Project.DerivedCategories
