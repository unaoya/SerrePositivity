module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeIsoFiberImageLaws
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTriangleFiberIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIso

/-!
概要：元の三角形比較と共通長辺の等式を、指定相対同型の fiber 像として揃える。
方針：両端の同じ正規化を照合し、長辺の等式を消去して恒等の場合へ戻す。
規約：元の三角形・長辺・指定値を保持。使われ方：模型 path の二三角形表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)

/-- 元の実際の fiber 三角形比較は同じ相対三角形比較の正規化した fiber 像。 -/
lemma coherentTransformationTriangleFiberIso_eq_image :
    coherentTransformationTriangleFiberIso F G J x y T b =
      relativeIsoFiberImage (smallLeftUnstraighteningProjection J)
        (smallLeftUnstraighteningProjection F)
        (coherentTransformationTotalMap_projection F J T.diagonal)
        (by rw [Category.assoc, coherentTransformationTotalMap_projection,
          coherentTransformationTotalMap_projection])
        (coherentTransformationTriangleRelativeIso F G J x y T) b := rfl

/-- 元の共通長辺の等式からの同型の fiber 像は同じ fiber 射の等式からの同型。 -/
lemma coherentTransformationRelativeEq_fiberImage
    {z z' : (leftUnstraighteningTransformationSpace F J) _⦋0⦌} (h : z = z') :
    relativeIsoFiberImage (smallLeftUnstraighteningProjection J)
      (smallLeftUnstraighteningProjection F)
      (coherentTransformationTotalMap_projection F J z)
      (coherentTransformationTotalMap_projection F J z')
      (eqToIso (congrArg SSet.HomotopyCategory.mk
        (congrArg (coherentTransformationRelativeVertex F J) h))) b =
    functorEqIso (congrArg (fun t => vertexFiberMap (smallLeftUnstraighteningProjection F)
      (smallLeftUnstraighteningProjection J) (coherentTransformationTotalMap F J t)
      (coherentTransformationTotalMap_projection F J t) b) h) := by
  subst z'
  exact relativeIsoFiberImage_refl _ _ _ b

end SerrePositivity.InfinityCategories.F2
