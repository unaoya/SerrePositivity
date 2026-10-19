module
public import SerrePositivity.InfinityCategories.Derived.DGModuleCofiberFiberContraction

/-! # cofiber と fiber の比較の合成の実原始元

概要：逆射の後の比較と恒等の差を全 Hom end の境界として表す。
方針：fiber の逆座標へ (−snd⋅h,0) を入れ、行列微分と分解式を使う。
規約：次数 −1 の明示成分。使われ方：β3 の比較辺の ∞ 同値性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 比較のもう一方の合成の差を解く次数 −1 成分。 -/
def dgModuleCofiberFiberHomotopyElement (f : M ⟶ N) :
    GradedHom A (dgModuleFiber A D (moduleConeInr A D f))
      (dgModuleFiber A D (moduleConeInr A D f)) (-1) :=
  (dgModuleFiberHomCoordinates A D
    (ForgetEnrichment.of (Complex A) (dgModuleFiber A D (moduleConeInr A D f)))
    (moduleConeInr A D f) (-2)).symm (-dgModuleCofiberFiberContractionN A D f, 0)

/-- 原始元の微分の二つの実座標。 -/
lemma dgModuleCofiberFiberHomotopyElement_differential_coordinates (f : M ⟶ N) :
    (moduleHom A D (dgModuleFiber A D (moduleConeInr A D f))
      (dgModuleFiber A D (moduleConeInr A D f))).d (-1) 0
        (dgModuleCofiberFiberHomotopyElement A D f) =
      (dgModuleFiberHomCoordinates A D
        (ForgetEnrichment.of (Complex A) (dgModuleFiber A D (moduleConeInr A D f)))
        (moduleConeInr A D f) (-1)).symm
        (compose A (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val
          (dgModuleCofiberFiberRetractElement A D f) (zero_add 0) -
            dgModuleFiberProjectionElement A D (moduleConeInr A D f),
         -compose A (moduleConeInrElement A D f) (dgModuleCofiberFiberContractionN A D f)
          (add_zero (-1))) := by
  have h := dgModuleFiberHomCoordinates_symm_differential A D
    (T := ForgetEnrichment.of (Complex A) (dgModuleFiber A D (moduleConeInr A D f)))
    (moduleConeInr A D f) (-2) (-dgModuleCofiberFiberContractionN A D f) 0
  have hneg : (moduleHom A D (dgModuleFiber A D (moduleConeInr A D f))
      (ForgetEnrichment.to (Complex A) N)).d (-1) 0
      (-dgModuleCofiberFiberContractionN A D f) =
      -(moduleHom A D (dgModuleFiber A D (moduleConeInr A D f))
        (ForgetEnrichment.to (Complex A) N)).d (-1) 0
          (dgModuleCofiberFiberContractionN A D f) := map_neg _ _
  have hc := compose_sub_right (A := A) (moduleConeInrElement A D f)
    (0 : GradedHom A (dgModuleFiber A D (moduleConeInr A D f))
      (ForgetEnrichment.to (Complex A) N) (-1))
    (dgModuleCofiberFiberContractionN A D f) (add_zero (-1))
  simp only [zero_sub, compose_zero] at hc
  change (moduleHom A D (dgModuleFiber A D (moduleConeInr A D f))
    (dgModuleFiber A D (moduleConeInr A D f))).d (-1) 0
      (dgModuleCofiberFiberHomotopyElement A D f) =
    (dgModuleFiberHomCoordinates A D
      (ForgetEnrichment.of (Complex A) (dgModuleFiber A D (moduleConeInr A D f)))
      (moduleConeInr A D f) (-1)).symm
      ((moduleHom A D (dgModuleFiber A D (moduleConeInr A D f))
        (ForgetEnrichment.to (Complex A) N)).d (-1) 0
          (-dgModuleCofiberFiberContractionN A D f),
       compose A (moduleConeInrElement A D f) (-dgModuleCofiberFiberContractionN A D f)
         (add_zero (-1)) -
       (moduleHom A D (dgModuleFiber A D (moduleConeInr A D f))
         (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d (-2) (-1) 0) at h
  rw [hneg, dgModuleCofiberFiberContractionN_differential, hc, map_zero, sub_zero] at h
  rw [h]
  congr 2
  abel

end SerrePositivity.InfinityCategories
