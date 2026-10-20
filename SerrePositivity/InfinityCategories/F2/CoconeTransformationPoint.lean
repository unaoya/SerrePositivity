module

public import SerrePositivity.InfinityCategories.F2.CoconeTransformationVertex
public import SerrePositivity.InfinityCategories.F2.CoconeTransformationFatComparison

/-!
概要：指定した頂点の等式を保ち、元の余錐の変換の fat join 表示を計算する。
方針：頂点の Yoneda 族に全パラメータの比較式を適用する。
規約：余錐も指定頂点も選び直さない。
使われ方：ホモトピーから実現した余錐と元の変換の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K X : SSet.{u}} {f : K ⟶ X}

/-- 概要：元の余錐を指定頂点の余錐空間の点として表示する。
方針：指定された頂点の等式を fiber 条件に用いる。
規約：元の余錐そのもの。使われ方：頂点の実現に伴う等式の輸送。 -/
def coconeMappingPointAt (c : JoinCocone f) (z : X _⦋0⦌) (hv : c.vertex = z) :
    (coconeMappingSpace f z) _⦋0⦌ :=
  ⟨c, by rw [PinchedHom.constant_zero]; exact hv⟩

/-- 概要：元の余錐の変換の fat join 図式は元の join 表示の制限そのもの。
方針：全パラメータの比較の式と Yoneda の uncurry の一致を使う。
規約：指定頂点への等式を保持。使われ方：実現の相対ホモトピーの接続。 -/
lemma coconeTransformationPointAt_fatDiagram
    (c : JoinCocone f) (z : X _⦋0⦌) (hv : c.vertex = z) :
    constantTransformationFatDiagram (SSet.yonedaEquiv.symm
      ((coconeTransformationMap f z).app _ (coconeMappingPointAt c z hv))) =
        fatJoinComparison K Δ[0] ≫ c.val := by
  rw [← SSet.yonedaEquiv_symm_comp, coconeTransformationFatDiagram_comparison,
    SSet.yonedaEquiv_symm_comp]
  change fatJoinComparison K Δ[0] ≫ sliceUnderUncurry (SSet.yonedaEquiv.symm c) = _
  rw [sliceUnderUncurry_yoneda]

end SerrePositivity.InfinityCategories.F2
