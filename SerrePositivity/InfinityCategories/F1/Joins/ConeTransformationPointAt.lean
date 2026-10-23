module

public import SerrePositivity.InfinityCategories.F1.Joins.ConeTransformationVertex

/-!
概要：指定頂点への等式を保持して、元の錐の標準変換と円柱を表示する。
方針：頂点の等式で標準変換を輸送する。
規約：元の錐・図式・指定頂点を選び直さない。
使われ方：指定変換から実現した錐の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {K X : SSet.{u}} {f : K ⟶ X}

/-- 元の錐の標準変換を、指定された頂点への等式だけで輸送する。 -/
def coneTransformationPointAt (c : JoinCone f) (z : X _⦋0⦌) (hv : c.vertex = z) :
    (intervalMappingSpace (functorVertex (SSet.const z)) (functorVertex f)) _⦋0⦌ :=
  hv ▸ coneTransformationVertex c

/-- 指定頂点へ輸送しても、標準変換の全円柱は同じ元の錐の円柱。 -/
lemma coneTransformationPointAt_prism (c : JoinCone f) (z : X _⦋0⦌) (hv : c.vertex = z) :
    sourceConstantTransformationPrism
      (SSet.yonedaEquiv.symm (coneTransformationPointAt c z hv)) =
        fst (K ⊗ (Δ[1] : SSet.{u})) Δ[0] ≫ coneCylinderMap K ≫ c.val := by
  subst z
  exact coneTransformationVertex_prism c

end SerrePositivity.InfinityCategories
