module

public import SerrePositivity.AlgebraicGeometry.IntegralModelColimit
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
概要：整拡大を有限・有限表示の模型の Spec の実際の逆極限として表す。
方針：環の filtered colimit を op と右随伴 Spec の極限保存で移す。
規約：各段の基底への射には元の R-代数構造を使う。忠実平坦性は仮定しない。
使われ方：Rydh 3.10 の整全射の有限・有限表示段による近似。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- 整拡大の有限・有限表示模型の Spec の逆系。 -/
def integralModelSpecDiagram : (IntegralModelIndex R B)ᵒᵖ ⥤ Scheme.{u} :=
  (integralModelSmallDiagram R B).op ⋙ Scheme.Spec

/-- 元の Spec B と、模型の実際の構造射からなる cone。 -/
def integralModelSpecCone : Cone (integralModelSpecDiagram R B) :=
  Scheme.Spec.mapCone (integralModelSmallCocone R B).op

/-- 整拡大の実際の Spec は、有限・有限表示模型の Spec の逆極限。 -/
def integralModelSpecConeIsLimit [Algebra.IsIntegral R B] :
    IsLimit (integralModelSpecCone R B) :=
  isLimitOfPreserves Scheme.Spec (IsColimit.op (integralModelSmallCoconeIsColimit R B))

/-- 模型の元の R-代数構造を使う基底への射。 -/
def integralModelSpecBaseMap (i : IntegralModelIndex R B) :
    (integralModelSpecDiagram R B).obj (.op i) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap R ((equivSmallModel (IntegralModelCategory R B)).inverse.obj i).obj.left.obj))

/-- 模型の基底への射は有限。 -/
instance integralModelSpecBaseMap_isFinite (i : IntegralModelIndex R B) :
    IsFinite (integralModelSpecBaseMap R B i) := by
  apply (IsFinite.SpecMap_iff _).mpr
  change (algebraMap R ((equivSmallModel (IntegralModelCategory R B)).inverse.obj i).obj.left.obj).Finite
  exact RingHom.finite_algebraMap.mpr
    ((equivSmallModel (IntegralModelCategory R B)).inverse.obj i).property.1

/-- 模型の基底への射は局所有限表示。 -/
instance integralModelSpecBaseMap_locallyOfFinitePresentation (i : IntegralModelIndex R B) :
    LocallyOfFinitePresentation (integralModelSpecBaseMap R B i) := by
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
  change (algebraMap R ((equivSmallModel (IntegralModelCategory R B)).inverse.obj i).obj.left.obj).FinitePresentation
  exact RingHom.finitePresentation_algebraMap.mpr
    ((equivSmallModel (IntegralModelCategory R B)).inverse.obj i).property.2

/-- 極限 cone の射影は、模型の実際の B への準同型の Spec。 -/
theorem integralModelSpecCone_projection (i : IntegralModelIndex R B) :
    (integralModelSpecCone R B).π.app (.op i) =
      Spec.map ((integralModelSmallCocone R B).ι.app i) := rfl

/-- 射影と基底への射の合成は、元の R→B の Spec。 -/
theorem integralModelSpecCone_projection_comp (i : IntegralModelIndex R B) :
    (integralModelSpecCone R B).π.app (.op i) ≫ integralModelSpecBaseMap R B i =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  change Spec.map (CommRingCat.ofHom
    ((equivSmallModel (IntegralModelCategory R B)).inverse.obj i).obj.hom.hom.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R
      ((equivSmallModel (IntegralModelCategory R B)).inverse.obj i).obj.left.obj)) = _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact ((equivSmallModel (IntegralModelCategory R B)).inverse.obj i).obj.hom.hom.commutes r

/-- 元の Spec が基底上全射なら、各有限・有限表示段も基底上全射。 -/
theorem integralModelSpecBaseMap_surjective
    [hSurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    (i : IntegralModelIndex R B) : Surjective (integralModelSpecBaseMap R B i) := by
  letI : Surjective ((integralModelSpecCone R B).π.app (.op i) ≫
      integralModelSpecBaseMap R B i) := by
    rw [integralModelSpecCone_projection_comp]
    exact hSurj
  exact Surjective.of_comp (f := (integralModelSpecCone R B).π.app (.op i))
    (g := integralModelSpecBaseMap R B i)

end SerrePositivity.AlgebraicGeometry
