module
public import SerrePositivity.DifferentialGraded.Resolution.FixedObjectCategory
public import SerrePositivity.DifferentialGraded.Resolution.CycleCoverFunctor

/-! # 固定対象増大の比較と境界cellの移送

元のdg関手を対象写像に持つ比較。各段階の豊穣構造は独立したデータとして保持する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.FixedObjectAugmentation
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} [dD : DGCategory A D]
  {E : Type w} [dE : DGCategory A E]

structure Map (S : FixedObjectAugmentation A D D id)
    (T : FixedObjectAugmentation A E E id) (F : DGFunctor A D E) where
  hom (x y : D) : S.category.Hom x y ⟶ T.category.Hom (F.obj x) (F.obj y)
  map_id (x : D) : S.category.id x ≫ hom x x = T.category.id (F.obj x)
  map_comp (x y z : D) : S.category.comp x y z ≫ hom x z =
    (hom x y ⊗ₘ hom y z) ≫ T.category.comp (F.obj x) (F.obj y) (F.obj z)
  augmentation (x y : D) : hom x y ≫ T.map (F.obj x) (F.obj y) = S.map x y ≫ F.map x y

namespace Map
variable {S : FixedObjectAugmentation A D D id} {T : FixedObjectAugmentation A E E id}
  {F : DGFunctor A D E} (M : Map S T F)

def toDGFunctor : DGFunctor A S.Objects T.Objects where
  obj x := ⟨F.obj x.val⟩
  map x y := M.hom x.val y.val
  map_id x := M.map_id x.val
  map_comp x y z := M.map_comp x.val y.val z.val

/-- 比較はcycleと指定原始元を同時に送り、境界cellの次数を保存する。 -/
def cellMap (i : S.CellIndex) : T.CellIndex := by
  refine ⟨F.obj i.1, F.obj i.2.1, i.2.2.degree,
    complexMapCycle A (M.hom i.1 i.2.1) _ i.2.2.cycle,
    (F.map i.1 i.2.1).f i.2.2.degree i.2.2.primitive, ?_⟩
  have hc := congrArg (fun f => f i.2.2.primitive)
    ((F.map i.1 i.2.1).comm i.2.2.degree (i.2.2.degree + 1))
  change (homObject A E (F.obj i.1) (F.obj i.2.1)).d _ _
    ((F.map i.1 i.2.1).f _ i.2.2.primitive) =
    (F.map i.1 i.2.1).f _ ((homObject A D i.1 i.2.1).d _ _ i.2.2.primitive) at hc
  have hb := i.2.2.boundary
  change (homObject A D i.1 i.2.1).d _ _ i.2.2.primitive = _ at hb
  rw [hb] at hc
  have hm := congrArg (fun f => f.f (i.2.2.degree + 1) i.2.2.cycle.val)
    (M.augmentation i.1 i.2.1)
  exact hc.trans hm.symm

lemma cellMap_degree (i : S.CellIndex) : (M.cellMap i).2.2.degree = i.2.2.degree := rfl

lemma cellMap_primitive (i : S.CellIndex) :
    (M.cellMap i).2.2.primitive = (F.map i.1 i.2.1).f i.2.2.degree i.2.2.primitive := rfl

end Map
end SerrePositivity.DifferentialGraded.FixedObjectAugmentation
