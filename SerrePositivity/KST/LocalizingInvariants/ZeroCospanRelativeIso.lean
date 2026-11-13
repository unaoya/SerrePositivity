module

public import SerrePositivity.KST.LocalizingInvariants.ZeroCospanHomotopyUniqueness
public import SerrePositivity.KST.LocalizingInvariants.FullyFaithfulIsoTransport

/-!
概要：同じ第一枝を持つ零第二枝 cospan の同型を、第一枝で恒等の証拠とともに構成する。
方針：第一枝射影の充満忠実性で恒等同型を持ち上げ、元の全図式へ含める。
規約：相対条件を選択する型に含める。使われ方：右辺を固定した fiber 正方形の正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.ZeroCospan

variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X]
  (F G : (horn 2 2 : SSet.{u}) ⟶ X)
  (hF : zeroSecond X (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) (hG : zeroSecond X (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
  (L : (Δ[1] : SSet.{u}) ⟶ X) (hFL : horn₂₂.ι₀₂ ≫ F = L) (hGL : horn₂₂.ι₀₂ ≫ G = L)

structure FirstRelativeIso where
  iso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G
  first_arrow : Arrow.mk (homPre horn₂₂.ι₀₂ iso.hom) =
    Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L)))

include hFL in
lemma firstVertex_eq : (hoFunctor.map (first X)).toFunctor.obj
    (HomotopyCategory.mk (vertex F hF)) = HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L) := by
  change HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₂.ι₀₂ ≫ F)) = _
  exact congrArg (fun k ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex k)) hFL

def firstRelativeIso : FirstRelativeIso F G L := by
  let T := (hoFunctor.map (first X)).toFunctor
  let hx := firstVertex_eq F hF L hFL
  let hy := firstVertex_eq G hG L hGL
  let e := transportedPreimageIso T (first_isFullyFaithful X).toHoFullyFaithful hx hy
    (Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L)))
  let E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G := (hoFunctor.map (inclusion X)).toFunctor.mapIso e
  refine ⟨E, ?_⟩
  change Arrow.mk (((hoFunctor.map (inclusion X)).toFunctor ⋙
    (hoFunctor.map ((pre horn₂₂.ι₀₂).app X)).toFunctor).map e.hom) = _
  rw [← Cat.Hom.comp_toFunctor, ← hoFunctor.map_comp]
  change Arrow.mk (T.map e.hom) = _
  exact transportedPreimageIso_map_arrow T (first_isFullyFaithful X).toHoFullyFaithful hx hy _

end SerrePositivity.KST.LocalizingInvariants.ZeroCospan
