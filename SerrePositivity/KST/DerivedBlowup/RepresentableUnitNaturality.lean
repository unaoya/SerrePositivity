module

public import SerrePositivity.KST.DerivedBlowup.RepresentableUnitMap
public import SerrePositivity.DifferentialGraded.Module.RestrictionRepresentable

/-!
概要：KST §3.1 の指定閉零 Yoneda 拡張の加群射・係数制限に関する自然性。
方針：斉次作用公式を用い、全次数自然性または指定 Hom 写像へ戻す。
規約：局所 regular 比較の指定経路を保持する。
使われ方：構造加群の canonical な cartesian 比較との整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open DifferentialGraded

variable (R : Type u) [CommRing R] {C : Type v} [DGCategory R C] [Small.{u} C]

set_option maxHeartbeats 2000000 in
-- 主 Hom の閉零射の成分と全次数作用の自然性を照合するために必要。
/-- 概要：指定閉零 Yoneda 拡張は値域加群の射による後合成と整合する。
方針：各成分を斉次要素で評価し、加群射の全次数自然性を使う。
規約：KST §3.1。使われ方：局所制限比較と regular 比較の可換式。 -/
theorem representableUnitMap_postcomp (x : C) {M N : ModuleCategory R C}
    (ψ : 𝟙_ (Complex R) ⟶ (ForgetEnrichment.to (Complex R) M).obj (op x)) (f : M ⟶ N) :
    representableUnitMap R x (ForgetEnrichment.to (Complex R) M) ψ ≫ f =
      representableUnitMap R x (ForgetEnrichment.to (Complex R) N)
        (ψ ≫ (moduleEvaluation R C x).map f) := by
  apply moduleMorphism_ext
  intro y
  rw [CategoryTheory.Functor.map_comp]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change GradedHom R y x q at h
  change ((moduleEvaluation R C y).map f).f q
      ((((moduleEvaluation R C y).map
        (representableUnitMap R x (ForgetEnrichment.to (Complex R) M) ψ)).f q) h) = _
  rw [representableUnitMap_apply]
  have hf := closedFamily_action R
    (closedTransApp R (moduleClosedHomEquiv R C M N f))
    (closedTransApp_naturality R (moduleClosedHomEquiv R C M N f))
    (op x) (op y) q 0 q (zero_add q) h (cycleFromUnit _ ψ).val
  calc
    _ = moduleAction R (ForgetEnrichment.to (Complex R) N) (x := op x) (y := op y) h
        (cycleFromUnit _ (ψ ≫ (moduleEvaluation R C x).map f)).val (zero_add q) := hf
    _ = _ := (representableUnitMap_apply R x (ForgetEnrichment.to (Complex R) N)
      (ψ ≫ (moduleEvaluation R C x).map f) y q h).symm

variable {D : Type w} [DGCategory R D] [Small.{u} D]

set_option maxHeartbeats 2000000 in
-- 代表制限比較と二つの Yoneda 拡張の斉次作用を照合するために必要。
/-- 概要：指定閉零 Yoneda 拡張は Hom 写像による代表制限比較と整合する。
方針：各成分で指定 dg 関手の Hom 写像と制限加群の作用の定義を比較する。
規約：KST §3.1。使われ方：局所 regular 生成元の係数遷移。 -/
theorem representableUnitMap_restrict (F : DGFunctor R C D) (x : C) (M : RightModule R D)
    (ψ : 𝟙_ (Complex R) ⟶ M.obj (op (F.obj x))) :
    representableUnitMap R x (restrictModule R C D F.op M) ψ =
      representableRestrictionMap R C D F x ≫
        (moduleRestriction R C D F.op).map (representableUnitMap R (F.obj x) M ψ) := by
  apply moduleMorphism_ext
  intro y
  rw [CategoryTheory.Functor.map_comp, representableRestrictionMap_eval,
    moduleRestriction_map_eval]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change (((moduleEvaluation R C y).map
      (representableUnitMap R x (restrictModule R C D F.op M) ψ)).f q) h =
    (((moduleEvaluation R D (F.obj y)).map
      (representableUnitMap R (F.obj x) M ψ)).f q) ((F.map y x).f q h)
  rw [representableUnitMap_apply, representableUnitMap_apply]
  rfl

end SerrePositivity.KST.DerivedBlowup
