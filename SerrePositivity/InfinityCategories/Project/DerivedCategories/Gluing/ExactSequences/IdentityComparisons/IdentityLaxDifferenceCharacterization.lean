module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.LocalizationProjectionComparison
public import SerrePositivity.KST.LocalizingInvariants.IdentityLaxVerdier
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceDComparison
/-!
概要：完全な恒等 lax 関手が対角を零化し、右因子上で恒等なら、選択 cofiber 差と全関手同型を持つ。
方針：恒等 lax Verdier 列の局所化普遍性と同じ右切断を使う。
規約：cone 関手の存在を仮定で代用しない。使われ方：実 cone 関手との全比較の判定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet
open scoped _root_.Simplicial
open _root_.SerrePositivity.KST.LocalizingInvariants
variable (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})

def identityLaxDifferenceCharacterization
    (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory (𝟙 C) (𝟙 C)) C)
    (hz : ∀ x, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((IdentityLax.exactDiagonal C).hom ≫ r.hom).app
      (Opposite.op ⦋0⦌) x))
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (LaxInclusion.fromD (𝟙 C) (𝟙 C) ≫ r.hom) (𝟙 C.obj)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso r.hom (exactLaxDifference (𝟙 C) (𝟙 C)).hom :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.localizationProjectionComparison (exactLaxDifference (𝟙 C) (𝟙 C)).hom
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (IdentityLax.exactDiagonal C)))
    (IdentityLax.difference_isVerdier C).quotient
    (LaxInclusion.fromD (𝟙 C) (𝟙 C)) (fromD_differenceIso (𝟙 C) (𝟙 C))
    r.hom ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.inverts_iff_kills_inclusion (IdentityLax.exactDiagonal C) r).mpr hz) hr

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
