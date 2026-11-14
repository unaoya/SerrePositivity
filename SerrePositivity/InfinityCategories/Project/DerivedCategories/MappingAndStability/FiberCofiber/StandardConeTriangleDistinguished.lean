module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.StandardCofiberTriangleImage

/-! # 標準 cone 三角形の distinguished 性

概要：零な直和成分を省いた三角形を、Mathlib の cone 三角形と同定する。
方針：第二頂点だけを直和包含の同型で変更する。
規約：接続射の符号は Mathlib のもの。使われ方：D7 の標準 cofiber 三角形の保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Pretriangulated Limits DifferentialGraded
open scoped _root_.Simplicial ZeroObject
variable {S : Type u} [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]
variable {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}

/-- 第二頂点の零直和を戻すと通常の cone 三角形になる。 -/
def derivedStandardConeTriangleIso (f : X.val ⟶ Y.val) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStandardConeTriangle f ≅
      DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference f (0 : X.val ⟶ 0))) := by
  refine Triangle.isoMk _ _ (Iso.refl _)
    (DerivedCategory.Q.mapIso (isoBiprodZero (X := Y.val) (isZero_zero _))) (Iso.refl _)
    ?_ ?_ ?_
  · change DerivedCategory.Q.map f ≫ DerivedCategory.Q.map biprod.inl =
      𝟙 _ ≫ DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference f (0 : X.val ⟶ 0))
    rw [Category.id_comp, ← DerivedCategory.Q.map_comp]
    congr 1
    apply biprod.hom_ext <;> simp [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference]
  · change DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB f (0 : X.val ⟶ 0)) ≫ 𝟙 _ =
      DerivedCategory.Q.map biprod.inl ≫ DerivedCategory.Q.map
        (CochainComplex.mappingCone.inr (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference f (0 : X.val ⟶ 0)))
    rw [Category.comp_id, ← DerivedCategory.Q.map_comp]
    rfl
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStandardConeTriangle, Triangle.mk_mor₃, Iso.refl_hom,
      CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
    rfl

/-- 標準 cone 三角形は distinguished。 -/
lemma derivedStandardConeTriangle_distinguished (f : X.val ⟶ Y.val) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStandardConeTriangle f ∈ distTriang (DerivedCategory (ModuleCat S)) :=
  isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.cofiberDifference f (0 : X.val ⟶ 0))) _ (derivedStandardConeTriangleIso f)

/-- D3 は実際の標準 cofiber 三角形を distinguished triangle に写す。 -/
lemma derivedStandardCofiberTriangle_distinguished (f : X.val ⟶ Y.val) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.mapTriangle.obj
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_isCofiberSequence f)) ∈
      distTriang (DerivedCategory (ModuleCat S)) :=
  isomorphic_distinguished _ (derivedStandardConeTriangle_distinguished f) _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStandardCofiberTriangleImageIso f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
