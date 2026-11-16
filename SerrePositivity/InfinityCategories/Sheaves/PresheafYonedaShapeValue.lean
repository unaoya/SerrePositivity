module

public import SerrePositivity.InfinityCategories.Sheaves.PresheafYonedaShapeIso

/-!
概要：指定した前層形状の同型の逆射を、同じ前層全体の前合成として計算する。
方針：内部 Hom の第一変数の作用を、関手頂点と反対の頂点で評価する。
規約：元の全関手を保持し、対象ごとの別々の移送を選ばない。
使われ方：HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）、S8 の離散重みの比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable (C : Type u) [SmallCategory C]

/-- 同じ前層頂点の形状移送は、元の指定した反対 nerve の写像との前合成。
HTT 5.1.5.6、内部 Hom の同じ第一変数の評価の法則。 -/
lemma fixedPresheafShapeIso_inv_vertex (F : Presheaf C SpaceInfinity.{u}) :
    (fixedPresheafShapeIso C).inv.app (Opposite.op ⦋0⦌) (functorVertex F) =
      functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ F) := by
  rfl

/-- 同じ反対前層頂点の形状移送も、同じ前合成の反対の頂点。
HTT 5.1.5.6、反転と内部 Hom の評価の法則。 -/
lemma fixedPresheafShapeIso_op_inv_vertex (F : Presheaf C SpaceInfinity.{u}) :
    (SSet.opFunctor.mapIso (fixedPresheafShapeIso C)).inv.app (Opposite.op ⦋0⦌)
        (SSet.opObjEquiv.symm (functorVertex F)) =
      SSet.opObjEquiv.symm (functorVertex
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).hom ≫ F)) := by
  rfl

end SerrePositivity.InfinityCategories.Sheaves
