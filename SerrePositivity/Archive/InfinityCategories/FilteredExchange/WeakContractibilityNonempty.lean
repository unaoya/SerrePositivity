module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.WeakContractibility
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty

/-!
概要：弱可縮な単体集合は頂点を持つ。
方針：頂点が無ければホーン充填は空虚に成立し、弱同値の Kan 逆から矛盾する。
規約：元の単体集合の Kan 性は仮定しない。
使われ方：弱可縮な coslice から余錐の存在を回収する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：頂点を持たない単体集合は Kan 複体。
方針：各ホーンの面から頂点が写るため、充填問題の存在自体が矛盾する。
規約：零次元のホーンは試験しない。使われ方：弱可縮性から非空性への反映。 -/
lemma kanComplex_of_not_nonempty {X : SSet.{u}} (hX : ¬ X.Nonempty) : KanComplex X := by
  apply SSet.KanComplex.iff.2
  intro n i f _
  obtain ⟨j, hj⟩ := exists_ne i
  exact (hX (SSet.nonempty_of_hom (f j hj))).elim

/-- 概要：任意の弱可縮な単体集合は頂点を持つ。
方針：空なら Kan 性を得て、一点への弱同値のホモトピー逆から頂点を戻す。
規約：弱可縮性を Kan 性込みの定義へ変更しない。
使われ方：coslice の弱可縮性による filtered 性の必要十分条件。 -/
lemma nonempty_of_isWeaklyContractible {X : SSet.{u}} (hX : IsWeaklyContractible X) :
    X.Nonempty := by
  by_contra hn
  have := kanComplex_of_not_nonempty hn
  have := isContractibleKan_terminal.{u}.kanComplex
  obtain ⟨g, _, _⟩ := hX.isSimplicialHomotopyEquivalence
  have := isContractibleKan_terminal.{u}.nonempty
  exact hn (SSet.nonempty_of_hom g)

end SerrePositivity.InfinityCategories.F2
