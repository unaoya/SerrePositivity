module
public import SerrePositivity.InfinityCategories.Derived.StandardCofiberTriangleImage

/-! # 標準 cone 三角形の distinguished 性

概要：零な直和成分を省いた三角形を、Mathlib の cone 三角形と同定する。
方針：第二頂点だけを直和包含の同型で変更する。
規約：接続射の符号は Mathlib のもの。使われ方：D7 の標準 cofiber 三角形の保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Pretriangulated Limits DifferentialGraded DGNerve
open scoped Simplicial ZeroObject
variable {S : Type u} [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]
variable {X Y : Semifree S}

/-- 第二頂点の零直和を戻すと通常の cone 三角形になる。 -/
def derivedStandardConeTriangleIso (f : X.val ⟶ Y.val) :
    derivedStandardConeTriangle f ≅
      DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
        (cofiberDifference f (0 : X.val ⟶ 0))) := by
  refine Triangle.isoMk _ _ (Iso.refl _)
    (DerivedCategory.Q.mapIso (isoBiprodZero (X := Y.val) (isZero_zero _))) (Iso.refl _)
    ?_ ?_ ?_
  · change DerivedCategory.Q.map f ≫ DerivedCategory.Q.map biprod.inl =
      𝟙 _ ≫ DerivedCategory.Q.map (cofiberDifference f (0 : X.val ⟶ 0))
    rw [Category.id_comp, ← DerivedCategory.Q.map_comp]
    congr 1
    apply biprod.hom_ext <;> simp [cofiberDifference]
  · change DerivedCategory.Q.map (pushoutInclusionB f (0 : X.val ⟶ 0)) ≫ 𝟙 _ =
      DerivedCategory.Q.map biprod.inl ≫ DerivedCategory.Q.map
        (CochainComplex.mappingCone.inr (cofiberDifference f (0 : X.val ⟶ 0)))
    rw [Category.comp_id, ← DerivedCategory.Q.map_comp]
    rfl
  · simp only [derivedStandardConeTriangle, Triangle.mk_mor₃, Iso.refl_hom,
      CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
    rfl

/-- 標準 cone 三角形は distinguished。 -/
lemma derivedStandardConeTriangle_distinguished (f : X.val ⟶ Y.val) :
    derivedStandardConeTriangle f ∈ distTriang (DerivedCategory (ModuleCat S)) :=
  isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished
    (cofiberDifference f (0 : X.val ⟶ 0))) _ (derivedStandardConeTriangleIso f)

/-- D3 は実際の標準 cofiber 三角形を distinguished triangle に写す。 -/
lemma derivedStandardCofiberTriangle_distinguished (f : X.val ⟶ Y.val) :
    (derivedStableHomotopyEquivalence S).functor.mapTriangle.obj
        (cofiberTriangle (semifreeCofiberZeroTriangle f)
          (semifreeCofiberZeroTriangle_isCofiberSequence f)) ∈
      distTriang (DerivedCategory (ModuleCat S)) :=
  isomorphic_distinguished _ (derivedStandardConeTriangle_distinguished f) _
    (derivedStandardCofiberTriangleImageIso f)

end SerrePositivity.InfinityCategories
