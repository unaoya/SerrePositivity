module

public import SerrePositivity.InfinityCategories.F2.CoconeTransformationPoint

/-!
概要：指定頂点で正規化した元の余錐の標準変換の全円柱を、元の余錐の円柱で計算する。
方針：標準比較の全族の prism 公式を元の指定余錐の Yoneda 族へ適用する。
規約：元の余錐と頂点の等式を保持。使われ方：実際の相対 join fiber 余錐の単位比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ指定頂点で読む元の余錐の標準変換は、元の余錐の全円柱を厳密に回収する。 -/
lemma coconeTransformationPointAt_prism {K X : SSet.{u}} {f : K ⟶ X}
    (c : JoinCocone f) (z : X _⦋0⦌) (hv : c.vertex = z) :
    F2.constantTransformationPrism (SSet.yonedaEquiv.symm
      ((F2.coconeTransformationMap f z).app (Opposite.op ⦋0⦌)
        (F2.coconeMappingPointAt c z hv))) = joinCylinderMap K Δ[0] ≫ c.val := by
  rw [← SSet.yonedaEquiv_symm_comp, F2.coconeTransformationMap_prism,
    F2.coconeParameterPrism, SSet.yonedaEquiv_symm_comp]
  change joinCylinderMap K Δ[0] ≫ sliceUnderUncurry (SSet.yonedaEquiv.symm c) = _
  rw [sliceUnderUncurry_yoneda]

end SerrePositivity.InfinityCategories.F2.Ind
