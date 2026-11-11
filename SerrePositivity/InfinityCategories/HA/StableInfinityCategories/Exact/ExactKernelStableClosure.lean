module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure

/-!
概要：完全関手の核として同定された本質像は、元の実頂点の安定閉包で変わらない。
方針：完全関手の安定閉包の零化と、核の両方向の同定を使う。
規約：包含の本質像をより大きい集合へ変更しない。使われ方：既存の実 cofiber 分母計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact
open _root_.SerrePositivity.KST.LocalizingInvariants

lemma stableClosure_eq_of_exact_kernel {A T B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A T) (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap T B)
    (hk : ∀ x, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.hom.app (Opposite.op ⦋0⦌) x) ↔ x ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) :
    {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) x} = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i := by
  ext x
  constructor
  · intro hx
    exact (hk x).mp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kills_stableVertexClosure F.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i)
      (fun y hy => (hk y).mpr hy) hx)
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem

lemma cofiberEdges_stableClosure_eq_of_exact_kernel {A T B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A T) (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap T B)
    (hk : ∀ x, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.hom.app (Opposite.op ⦋0⦌) x) ↔ x ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) x} =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage i) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.stableClosure_eq_of_exact_kernel i F hk]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.cofiberEdges_stableClosure_eq_of_exact_kernel := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.cofiberEdges_stableClosure_eq_of_exact_kernel

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableClosure_eq_of_exact_kernel := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.stableClosure_eq_of_exact_kernel
