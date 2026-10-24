module

public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.InfinityCategories.Core.InitialTransport
public import SerrePositivity.InfinityCategories.Core.HomotopyBoundaryExtension

/-! General declarations moved verbatim from their original modules. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 概要：quasicategory の同値は始頂点を始頂点へ送る。
方針：逆射で境界を充填し、単位の可逆二胞体で元の境界に戻す。
規約：最初の頂点の条件を保つ。使われ方：余極限の模型の比較。 -/
lemma QCatEquivalence.map_isInitialVertex {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) {x : X _⦋0⦌}
    (hx : IsInitialVertex x) : IsInitialVertex (e.hom.app (Opposite.op ⦋0⦌) x) := by
  intro n b hb
  have hi := FunctorIso.app e.homInvIso x
  have hterm : IsInitialVertex (e.inv.app (Opposite.op ⦋0⦌)
      (e.hom.app (Opposite.op ⦋0⦌) x)) := hx.of_vertexIso hi.symm
  have hb' : boundaryVertex n (0) ≫ (b ≫ e.inv) =
      SSet.yonedaEquiv.symm (e.inv.app (Opposite.op ⦋0⦌)
        (e.hom.app (Opposite.op ⦋0⦌) x)) := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
  obtain ⟨F, hF⟩ := hterm n (b ≫ e.inv) hb'
  have hF' : (boundary (n + 1)).ι ≫ (F ≫ e.hom) = b ≫ (e.inv ≫ e.hom) := by
    rw [← Category.assoc, hF, Category.assoc]
  have he : FunctorIso (b ≫ (e.inv ≫ e.hom)) b := by
    simpa only [Category.comp_id] using FunctorIso.precomp e.invHomIso b
  exact FunctorIso.exists_boundaryFilling he ⟨F ≫ e.hom, hF'⟩


/-- 概要：quasicategory の同値は始対象性を保ち反映する。
方針：逆同値で始対象性を戻し、単位の頂点での同型で元の頂点へ移す。
規約：任意の頂点 x を扱う。
使われ方：HTT §1.2.12、Kerodon §7.1 の始対象の同値不変性。 -/
lemma QCatEquivalence.isInitialVertex_iff {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) (x : X _⦋0⦌) :
    IsInitialVertex x ↔ IsInitialVertex (e.hom.app (Opposite.op ⦋0⦌) x) := by
  constructor
  · exact e.map_isInitialVertex
  · intro h
    exact (e.symm.map_isInitialVertex h).of_vertexIso (FunctorIso.app e.homInvIso x)


end SerrePositivity.InfinityCategories
