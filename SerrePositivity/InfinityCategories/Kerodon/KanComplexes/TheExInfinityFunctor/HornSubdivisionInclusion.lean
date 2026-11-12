module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornSubdivisionLastVertex
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionAdjunctionSimplex

/-!
# horn の包含と細分比較の可換性

概要：horn の細分比較は、標準単体への包含と面の順序集合への包含に関して可換である。
方針：随伴で Ex への写像に移し、各単体の有限鎖の像を計算する。
規約：Moss 2020 Proposition 21 の二重細分の境界の接続。
使われ方：候補の horn 上での境界条件を得る。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite PartialOrder
open scoped _root_.Simplicial

/--
概要：horn の単体の標準単体への包含は、その頂点写像に対応する標準単体の射である。
方針：Yoneda 同値で両辺を評価する。
規約：細分の自然性を標準単体の写像へ適用するための表示。
使われ方：horn の細分比較の包含との可換性。
-/
theorem hornSimplex_yoneda_inclusion (n : ℕ) (k : Fin (n + 1)) (d : SimplexCategory)
    (s : (SSet.horn.{u} n k).obj (op d)) :
    SSet.yonedaEquiv.symm s ≫ (SSet.horn n k).ι =
      SSet.stdSimplex.map (SSet.stdSimplex.objEquiv s.val) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_map, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply]
  rfl

/--
概要：horn の細分比較は標準単体への包含と可換である。
方針：随伴の各単体での公式と標準細分の同型の自然性を使う。
規約：二重細分の境界条件を面の部分順序集合へ移す比較正方形。
使われ方：二重細分から horn への候補の制限。
-/
@[reassoc] theorem hornSubdivisionComparison_inclusion (n : ℕ) (k : Fin (n + 1)) :
    SSet.sd.map (SSet.horn.{u} n k).ι ≫ SSet.stdSimplex.sdIso.hom.app ⦋n⦌ =
      hornSubdivisionComparison n k ≫ nerveMap (hornFaceInclusion n k).monotone.functor := by
  apply (SSet.sdExAdjunction.homEquiv _ _).injective
  conv_rhs => rw [SSet.sdExAdjunction.homEquiv_naturality_right]
  simp only [hornSubdivisionComparison, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  rw [subdivisionHomEquiv_app_down]
  calc
    _ = SSet.stdSimplex.sdIso.inv.app d.unop ≫
        (SSet.sd.map (SSet.yonedaEquiv.symm s ≫ (SSet.horn n k).ι) ≫
          SSet.stdSimplex.sdIso.hom.app ⦋n⦌) := by
      simp only [SSet.sd.map_comp, Category.assoc]
    _ = SSet.stdSimplex.sdIso.inv.app d.unop ≫
        (SSet.sd.map (SSet.stdSimplex.map (SSet.stdSimplex.objEquiv s.val)) ≫
          SSet.stdSimplex.sdIso.hom.app ⦋n⦌) := by rw [hornSimplex_yoneda_inclusion]
    _ = SimplexCategory.sd.map (SSet.stdSimplex.objEquiv s.val) := by
      have hn : SSet.sd.map (SSet.stdSimplex.map (SSet.stdSimplex.objEquiv s.val)) ≫
          SSet.stdSimplex.sdIso.hom.app ⦋n⦌ =
        SSet.stdSimplex.sdIso.hom.app d.unop ≫
          SimplexCategory.sd.map (SSet.stdSimplex.objEquiv s.val) :=
        SSet.stdSimplex.sdIso.hom.naturality (SSet.stdSimplex.objEquiv s.val)
      rw [hn]
      simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    _ = _ := by
      apply NatTrans.ext
      funext a
      apply ConcreteCategory.hom_ext
      intro t
      apply nerve.ext_of_isThin
      funext i
      rfl

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
