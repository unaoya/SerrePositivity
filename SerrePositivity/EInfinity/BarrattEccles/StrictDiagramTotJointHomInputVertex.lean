module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointHomRestriction
/-!
概要：元の二変数native Hom入力の頂点を、元の二つのCAlg源の頂点と合わせる。
方針：元の固定始域則を評価し、同じnerve頂点・直積射影・零次の定値則を使う。
規約：二つの端点を選び直さず、元のモデル源の頂点表示も保持する。
使われ方：同じnative fiber射と元のroof比較の両端の厳密な照合。
-/
@[expose] public noncomputable section
open CategoryTheory SSet
open SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A]
local instance jointHomInputVertexModel : HomotopicalAlgebra.ModelCategory (operad A).Algebra :=
  modelCategory A
/-- 同じ二変数の入力の頂点は、元のCAlg源の同じ両頂点の対。 -/
theorem strictBETotJointNativeHomInput_vertex (P : strictBETotJointHomIndex A) :
    (strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P) =
      (SSet.opObjEquiv.symm ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (AsSmall.down.obj P).1.unop)),
       (algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (AsSmall.down.obj P).2)) := by
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌)
    (nerveVertex ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).obj
      (AsSmall.down.obj P).2)))
    (strictBETotJointNativeHomInput_fixSource A (AsSmall.down.obj P).1.unop)
  have hp : (nerveMap (strictBETotJointHomFixSource A (AsSmall.down.obj P).1.unop)).app
      (Opposite.op ⦋0⦌)
        (nerveVertex ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).obj
          (AsSmall.down.obj P).2)) = nerveVertex P := ComposableArrows.ext₀ rfl
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  rw [hp] at h
  have hl {K L M : SSet.{u+1}} (f : K ⟶ L) (g : K ⟶ M)
      (s : K _⦋0⦌) :
      (CartesianMonoidalCategory.lift f g).app (Opposite.op ⦋0⦌) s =
        (f.app (Opposite.op ⦋0⦌) s, g.app (Opposite.op ⦋0⦌) s) := by
    apply Prod.ext
    · exact congrArg (fun t => t.app (Opposite.op ⦋0⦌) s)
        (CartesianMonoidalCategory.lift_fst f g)
    · exact congrArg (fun t => t.app (Opposite.op ⦋0⦌) s)
        (CartesianMonoidalCategory.lift_snd f g)
  have hz {K L : SSet.{u+1}} (y : L _⦋0⦌) (s : K _⦋0⦌) :
      (SSet.const y : K ⟶ L).app (Opposite.op ⦋0⦌) s = y := by
    change L.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op y = y
    rw [show SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ from Subsingleton.elim _ _,
      op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [hl, hz] at h
  change (strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P) =
    (SSet.opObjEquiv.symm ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (AsSmall.down.obj P).1.unop)),
     (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).obj
        (AsSmall.down.obj P).2))) at h
  exact h.trans (congrArg (fun z =>
    (SSet.opObjEquiv.symm ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (AsSmall.down.obj P).1.unop)), z))
        (strictBETotModelSource_vertex A (AsSmall.down.obj P).2))
/-- 同じ入力を元のモデル源の頂点で表示した厳密な等式。 -/
theorem strictBETotJointNativeHomInput_model_vertex (P : strictBETotJointHomIndex A) :
    (strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P) =
      (SSet.opObjEquiv.symm ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject
          (operad A).Algebra (AsSmall.down.obj P).1.unop))),
       (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject
          (operad A).Algebra (AsSmall.down.obj P).2))) := by
  rw [strictBETotModelSource_vertex, strictBETotModelSource_vertex]
  exact strictBETotJointNativeHomInput_vertex A P
end SerrePositivity.EInfinity.BarrattEccles
