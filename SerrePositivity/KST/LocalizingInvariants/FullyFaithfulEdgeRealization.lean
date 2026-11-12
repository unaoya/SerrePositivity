module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom

/-!
概要：充満忠実な ∞ 関手の像の指定射を、元の指定両端を持つ辺で実現する。
方針：ホモトピー圏の充満忠実性の逆像を、同じ射を表す実辺へ戻す。
規約：同じ Hom 内の射の類を保持。使われ方：標準区間 Hom の比較の逆移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

structure FullEdgeRealization {E B : SSet.{u}} (p : E ⟶ B) (x y : E _⦋0⦌)
    (α : HomotopyCategory.mk (p.app (Opposite.op ⦋0⦌) x) ⟶
      HomotopyCategory.mk (p.app (Opposite.op ⦋0⦌) y)) where
  path : E.Edge x y
  image : (hoFunctor.map p).toFunctor.map
    (Truncated.HomotopyCategory.homMk path.toTruncated) = α

def fullEdgeRealization {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p) (x y : E _⦋0⦌)
    (α : HomotopyCategory.mk (p.app (Opposite.op ⦋0⦌) x) ⟶
      HomotopyCategory.mk (p.app (Opposite.op ⦋0⦌) y)) : FullEdgeRealization p x y α := by
  let F := hp.toHoFullyFaithful
  let β := F.preimage (X := HomotopyCategory.mk x) (Y := HomotopyCategory.mk y) α
  let e := Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y β)
  have he := Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y β)
  refine ⟨SSet.Edge.ofTruncated e, ?_⟩
  exact (congrArg (fun k ↦ (hoFunctor.map p).toFunctor.map k) he).trans
    (F.map_preimage (X := HomotopyCategory.mk x) (Y := HomotopyCategory.mk y) α)

structure TransportedEdgeRealization {E B : SSet.{u}} (p : E ⟶ B) (x y : E _⦋0⦌)
    {x' y' : B _⦋0⦌} (hx : p.app (Opposite.op ⦋0⦌) x = x')
    (hy : p.app (Opposite.op ⦋0⦌) y = y') (α : HomotopyCategory.mk x' ⟶
      HomotopyCategory.mk y') where
  path : E.Edge x y
  image : Truncated.HomotopyCategory.homMk ((path.map p).ofEq hx hy).toTruncated = α

def transportedEdgeRealization {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p) (x y : E _⦋0⦌) {x' y' : B _⦋0⦌}
    (hx : p.app (Opposite.op ⦋0⦌) x = x') (hy : p.app (Opposite.op ⦋0⦌) y = y')
    (α : HomotopyCategory.mk x' ⟶ HomotopyCategory.mk y') :
    TransportedEdgeRealization p x y hx hy α := by
  let hf := congrArg HomotopyCategory.mk hx
  let hg := congrArg HomotopyCategory.mk hy
  let β := eqToHom hf ≫ α ≫ eqToHom hg.symm
  let R := fullEdgeRealization p hp x y β
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport hx hy
    (R.path.toTruncated.map ((truncation 2).map p))
    ((R.path.map p).ofEq hx hy).toTruncated rfl
  refine ⟨R.path, ?_⟩
  rw [← he]
  change eqToHom hf.symm ≫ (hoFunctor.map p).toFunctor.map
    (Truncated.HomotopyCategory.homMk R.path.toTruncated) ≫ eqToHom hg = α
  rw [R.image]
  simp only [β, Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants
