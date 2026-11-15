module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation

/-!
概要：有限型なイデアル層の閉包含の局所有限表示性。
方針：アフィン商の有限表示性を、閉部分スキームの標準アフィン被覆で貼り合わせる。
規約：基底の Noether 性を要求しない。
使われ方：有限表示の閉包絡の構成 C02 の局所判定。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u

/-- 全てのアフィン開で切断イデアルが有限生成であること。 -/
def IsFiniteTypeIdealSheaf {X : Scheme.{u}} (K : X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens, (K.ideal U).FG

set_option backward.isDefEq.respectTransparency false in
/-- 有限型イデアル層の閉包含は局所有限表示。Stacks 01TV (29.22.7)。 -/
theorem locallyOfFinitePresentation_subschemeι_of_finiteType
    {X : Scheme.{u}} (K : X.IdealSheafData) (hK : IsFiniteTypeIdealSheaf K) :
    LocallyOfFinitePresentation K.subschemeι := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation)
    K.subschemeCover.openCover
  intro U
  change LocallyOfFinitePresentation (K.subschemeCover.f U ≫ K.subschemeι)
  rw [K.subschemeCover_map_subschemeι, K.glueDataObjι_ι]
  let A : Type u := Γ(X, (U : X.affineOpens).1)
  let I := K.ideal U
  letI : Algebra.FinitePresentation A (A ⧸ I) := Algebra.FinitePresentation.quotient (hK U)
  have : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
    apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    change (algebraMap A (A ⧸ I)).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  infer_instance

end SerrePositivity.AlgebraicGeometry
