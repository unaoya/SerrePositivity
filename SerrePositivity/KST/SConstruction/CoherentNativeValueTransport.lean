module
public import SerrePositivity.KST.SConstruction.CoherentStringNativeMaps

/-! # 元の native Hom の値の対象表示を消去する
概要：対象の等式による native Hom の移送後の値が、元の豊穣作用の同じ値と依存等号で一致する。
方針：単体射の等号による移送を各成分で消去し、元の値へ戻す。
規約：新たな代表辺や同値を選ばず、全単体次数を保持する。
使われ方：元の K の二辺の因子分解列の値を指定した二合成へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 単体集合の等号による移送は、全次数の元の値と依存等号で一致する。 -/
lemma coherentEqToHom_value_heq {X Y : SSet.{u}} (h : X = Y) {d : ℕ} (x : X _⦋d⦌) :
    HEq ((eqToHom h).app (Opposite.op ⦋d⦌) x) x := by
  subst Y
  rfl

/-- 両端の表示を合わせた native 評価は、元の豊穣単体の同じ Path 評価に戻る。 -/
lemma coherentStringNativeMap_value_heq {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C)
    {x y : I} {f : x ⟶ y} (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) {d : ℕ}
    (P : (nerve (Path (ULift.up 0 : ULift.{u} (Fin (s.length + 1)))
      (ULift.up (Fin.last s.length)))) _⦋d⦌) :
    HEq ((coherentStringNativeMap Q s).app (Opposite.op ⦋d⦌) P)
      (((Q.app _ (ULift.up s.chain)).map (.mk (ULift.up 0))
        (.mk (ULift.up (Fin.last s.length)))).app (Opposite.op ⦋d⦌) P) := by
  dsimp only [coherentStringNativeMap, coherentStringDiagramCell, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.reobjectFunctor]
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
  exact (coherentEqToHom_value_heq _ _).trans (coherentEqToHom_value_heq _ _)

end SerrePositivity.KST.SConstruction
