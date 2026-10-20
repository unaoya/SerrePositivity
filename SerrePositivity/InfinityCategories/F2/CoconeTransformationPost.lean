module

public import SerrePositivity.InfinityCategories.F2.CoconeTransformationMap
public import SerrePositivity.InfinityCategories.F2.ConstantTransformationPost
public import SerrePositivity.InfinityCategories.F1.CosliceFiberPostcomposition

/-!
概要：native な余錐から変換空間への比較は標的関手の後合成に厳密に自然。
方針：全パラメータの円柱の両表示を比較し、円柱の一意性で結論する。
規約：圏内の辺による余錐の合成の整合性は別工程。
使われ方：coherent な余錐比較の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：標的関手で送った余錐の円柱は、元の円柱の後合成。
方針：fiber の後合成の包含と coslice の uncurry の自然性を使う。
規約：全パラメータで厳密に一致。使われ方：変換空間との比較の自然性。 -/
lemma coconeParameterPrism_postcomp {K X Y T : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}
    (a : T ⟶ coconeMappingSpace f z) (q : X ⟶ Y) :
    coconeParameterPrism (a ≫ coslicePostcompFiberMap f q z) = coconeParameterPrism a ≫ q := by
  rw [coconeParameterPrism, coconeParameterPrism, Category.assoc,
    coslicePostcompFiberMap_ι, ← Category.assoc a, sliceUnderUncurry_postcomp, Category.assoc]

/-- 概要：余錐から変換空間への比較は任意の標的関手に自然。
方針：両辺の円柱を元の余錐の円柱の後合成に同定する。
規約：同値類でなく実際の射の等式。使われ方：一般 coherent な余錐の比較。 -/
lemma coconeTransformationMap_postcomp {K X Y : SSet.{u}}
    (f : K ⟶ X) (z : X _⦋0⦌) (q : X ⟶ Y) :
    coslicePostcompFiberMap f q z ≫
        coconeTransformationMap (f ≫ q) (q.app (Opposite.op ⦋0⦌) z) =
      coconeTransformationMap f z ≫ constantTransformationPost f z q := by
  apply constantTransformationPrism_injective
  rw [coconeTransformationMap_prism, constantTransformationPost_prism]
  have h := coconeParameterPrism_postcomp (𝟙 (coconeMappingSpace f z)) q
  have he := coconeTransformationMap_prism (𝟙 (coconeMappingSpace f z))
  simp only [Category.id_comp] at h he
  rw [he]
  exact h

end SerrePositivity.InfinityCategories.F2
