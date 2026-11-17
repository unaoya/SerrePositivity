module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.NativeWeightedSections
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ConePoints

/-!
概要：元の重み付き錐空間とnative切断の同型が、同じ指定錐の零単体を保つことを示す。
方針：右随伴の一意性のcounit則を同じHom同値へ戻し、標準零単体を評価する。
規約：IS-W2 R02〜R03の既存の比較の点での法則。新しい錐の頂点は選ばない。
使われ方：元の普遍錐の点を同じBK重み制限へ接続する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.SerrePositivity.DiagramModel
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped _root_.Simplicial
variable (I : Type u) [SmallCategory I] (W : I ⥤ SSet.{u})

/-- 元の錐のHom同値は、同じテンソルの順序変更を通してnativeな転置に一致する。 -/
theorem coneSpaceNativeSectionsIso_homEquiv (X : SSet.{u}) (H : I ⥤ SSet.{u})
    (f : (WeightedCones.tensorDiagram I W).obj X ⟶ H) :
    (WeightedCones.adjunction I W).homEquiv X H f ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceNativeSectionsIso I W).hom.app H =
      weightedSectionsLift ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceParameterIso I W).inv.app X ≫ f) := by
  let adj1 := (WeightedCones.adjunction I W).ofNatIsoLeft (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceParameterIso I W)
  let adj2 := weightedSectionsAdjunction W
  let f' := (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceParameterIso I W).inv.app X ≫ f
  have h : adj1.homEquiv X H f' ≫ (Adjunction.rightAdjointUniq adj1 adj2).hom.app H =
      adj2.homEquiv X H f' := by
    apply (adj2.homEquiv X H).symm.injective
    rw [adj2.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_symm_rightAdjointUniq_hom_app,
      ← adj1.homEquiv_counit, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hn : adj2.homEquiv X H f' = weightedSectionsLift f' := by
    apply (weightedSectionsHomEquiv W H X).injective
    simp only [adj2, weightedSectionsAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
    exact ((weightedSectionsHomEquiv W H X).apply_symm_apply f').trans
      (weightedSectionsUncurry_lift f').symm
  rw [hn] at h
  simpa only [adj1, adj2, f', Adjunction.homEquiv_ofNatIsoLeft_apply,
    Iso.hom_inv_id_app_assoc, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceNativeSectionsIso]
    using h

/-- 元の同じ零単体テンソルの同型と順序変更は、nativeな第一射影。 -/
theorem coneSpaceParameterIso_zero :
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceParameterIso I W).inv.app (Δ[0] : SSet.{u}) ≫ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.zeroTensorWeightIso I W).hom =
      fst W ((Functor.const I).obj (Δ[0] : SSet.{u})) := by
  apply NatTrans.ext
  funext i
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨w, t⟩
  rfl

/-- 元の指定された錐の点は、同じnative切断の指定零単体へ移る。 -/
theorem coneSpaceNativeSectionsIso_point {H : I ⥤ SSet.{u}} (s : W ⟶ H) :
    (((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceNativeSectionsIso I W).hom.app H).app (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.conePoint I W s) =
      SSet.yonedaEquiv (weightedSectionsLift
        (fst W ((Functor.const I).obj (Δ[0] : SSet.{u})) ≫ s)) := by
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.conePoint, ← SSet.yonedaEquiv_comp, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceNativeSectionsIso_homEquiv,
    ← Category.assoc, _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceParameterIso_zero]
  rfl

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
