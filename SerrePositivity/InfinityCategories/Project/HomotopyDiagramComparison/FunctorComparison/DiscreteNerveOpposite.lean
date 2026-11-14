module

public import SerrePositivity.InfinityCategories.HA.Section5_2_2.ClassifiedConeLimit

/-!
概要：元の離散 nerve の反転を、元の同じ離散添字の厳密な同型で戻す。
方針：離散圏の単体の全頂点が同じ対象となることを使う。
規約：添字の有限性は不要。使われ方：元の圏の有限積と有限余積の双対化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の離散 nerve の反転は、同じ全単体を持つ元の離散 nerve と厳密に同型。 -/
def discreteNerveOppositeIso (J : Type u) :
    (nerve (Discrete J)).op ≅ nerve (Discrete J) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m α
    change (nerve (Discrete J)).op.map α = (nerve (Discrete J)).map α
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    change s.obj _ = s.obj _
    exact (IsDiscrete.eq_of_hom (s.map (homOfLE (Fin.zero_le _)))).symm.trans
      (IsDiscrete.eq_of_hom (s.map (homOfLE (Fin.zero_le _)))))

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
