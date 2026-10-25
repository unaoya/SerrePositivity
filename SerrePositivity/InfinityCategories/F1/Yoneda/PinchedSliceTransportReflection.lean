module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PinchedSlicePrismTransportIso
public import SerrePositivity.InfinityCategories.F1B.Equivalences.QCatEquivalenceOpposite

/-!
概要：元の slice 円柱の反対輸送が同値なら、同じ元の pinched Hom の作用も同値。
方針：円柱の輸送比較で両端の厳密な同型を消去し、二重反転の同型で元へ戻す。
規約：元の全係数写像と底辺を保持する。
使われ方：同じ表現可能前層による Hom 前合成の局所性判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
/-- 概要：指定底を持つ元の slice 円柱の反対輸送の同値性を、元の Hom 作用へ戻す。
方針：fiber 同型の消去と二重反転。規約：元の作用。使われ方：局所性の反映。 -/
lemma pinchedMap_isQCatEquivalence_of_slicePrism_transport {X : SSet.{u}} [Quasicategory X]
    (z : X _⦋0⦌) {x y : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x y)
    (c : pinchedHom y z ⟶ pinchedHom x z)
    (H : (Δ[1] : SSet.{u}) ⊗ pinchedHom y z ⟶ sliceOver (SSet.yonedaEquiv.symm z))
    (h₀ : prismEndpoint 0 _ ≫ H = c ≫ pinchedFamilySlice X x z)
    (h₁ : prismEndpoint 1 _ ≫ H = pinchedFamilySlice X y z)
    (hp : H ≫ sliceOverProjection _ = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e.edge)
    (ht : IsQCatEquivalence (edgeTransport
      (SSet.opFunctor.map (sliceOverProjection (SSet.yonedaEquiv.symm z))) (edgeOp e))) :
    IsQCatEquivalence c := by
  have hbase := (qCatEquivalenceOfIso (pinchedOppositeSliceFiberIso z y)).isQCatEquivalence.comp ht
  have h := hbase.ofFunctorIso (pinchedSlicePrism_oppositeTransportIso z e c H h₀ h₁ hp).symm
  have hc : IsQCatEquivalence (SSet.opFunctor.map c) :=
    (qCatEquivalenceOfIso (pinchedOppositeSliceFiberIso z x)).isQCatEquivalence.cancel_right h
  have hcc := F1B.isQCatEquivalence_op hc
  letI : Quasicategory ((SSet.opFunctor ⋙ SSet.opFunctor).obj (pinchedHom y z)) :=
    inferInstanceAs (Quasicategory (pinchedHom y z).op.op)
  letI : Quasicategory ((SSet.opFunctor ⋙ SSet.opFunctor).obj (pinchedHom x z)) :=
    inferInstanceAs (Quasicategory (pinchedHom x z).op.op)
  letI : Quasicategory ((𝟭 SSet.{u}).obj (pinchedHom y z)) :=
    inferInstanceAs (Quasicategory (pinchedHom y z))
  letI : Quasicategory ((𝟭 SSet.{u}).obj (pinchedHom x z)) :=
    inferInstanceAs (Quasicategory (pinchedHom x z))
  let α := SSet.opFunctorCompOpFunctorIso.app (pinchedHom y z)
  let β := SSet.opFunctorCompOpFunctorIso.app (pinchedHom x z)
  have hfin := hcc.comp (qCatEquivalenceOfIso β).isQCatEquivalence
  change IsQCatEquivalence (SSet.opFunctor.map (SSet.opFunctor.map c) ≫ β.hom) at hfin
  have hn : SSet.opFunctor.map (SSet.opFunctor.map c) ≫ β.hom = α.hom ≫ c := by
    exact (SSet.opFunctorCompOpFunctorIso.hom.naturality c).symm
  rw [hn] at hfin
  exact (qCatEquivalenceOfIso α).isQCatEquivalence.cancel_left hfin

end SerrePositivity.InfinityCategories
