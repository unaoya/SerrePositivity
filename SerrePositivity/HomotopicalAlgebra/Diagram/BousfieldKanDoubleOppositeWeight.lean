module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanWeightPost

/-!
概要：二重反対圏への標準再添字は、指定したBK重みの同型を与える。
方針：既存のweightPostを用い、Overへの二重反対とその逆の合成を確認する。
使われ方：HTT 4.2.4.4、RR02(a)の係数移送。
規約：元の重みの指定射を保持し、単なる圏同値でnerveの同型性を代用しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel
variable (I : Type u) [SmallCategory I]

/-- 標準の二重反対への重み比較は、指定された逆向きの後合成を逆に持つ。 -/
def bousfieldKanOpOpWeightIso : bousfieldKanWeight I ≅ opOp I ⋙ bousfieldKanWeight Iᵒᵖᵒᵖ where
  hom := bousfieldKanWeightPost (opOp I)
  inv := Functor.whiskerLeft (opOp I) (bousfieldKanWeightPost (unopUnop I))
  hom_inv_id := by
    apply NatTrans.ext
    funext i
    change nerveMap (Over.post (opOp I) (X := i)) ≫
      nerveMap (Over.post (unopUnop I) (X := Opposite.op (Opposite.op i))) = 𝟙 _
    exact (nerveFunctor.map_comp
      (Over.post (opOp I) (X := i)).toCatHom
      (Over.post (unopUnop I) (X := Opposite.op (Opposite.op i))).toCatHom).symm.trans
        (nerveFunctor.map_id (Cat.of (Over i)))
  inv_hom_id := by
    apply NatTrans.ext
    funext i
    change nerveMap (Over.post (unopUnop I) (X := Opposite.op (Opposite.op i))) ≫
      nerveMap (Over.post (opOp I) (X := i)) = 𝟙 _
    exact (nerveFunctor.map_comp
      (Over.post (unopUnop I) (X := Opposite.op (Opposite.op i))).toCatHom
      (Over.post (opOp I) (X := i)).toCatHom).symm.trans
        (nerveFunctor.map_id (Cat.of (Over (Opposite.op (Opposite.op i)))))

end SerrePositivity.DiagramModel
