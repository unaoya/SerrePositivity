module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialBoundaryHom

/-!
概要：相対始点境界を充填する二頂点間の比較射とその可逆性。
方針：指定始点からの Hom 全単射で比較射と逆射を持ち上げ、単射性で合成を検証する。
規約：全体での充満忠実性は要求しない。
使われ方：二つの普遍余錐を比較し、Kan 拡張間の比較射の各点での可逆性を示す。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：相対始点境界を充填する二頂点間の射は底への像が可逆なら可逆。
方針：底の逆射を Hom 全射性で持ち上げ、両合成を Hom 単射性で恒等射と同定する。
規約：両頂点でのみ相対始点境界充填を仮定する。
使われ方：普遍余錐間の射の可逆性の反映。 -/
lemma initialBoundaryHom_isIso_of_map {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) {x y : E _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p x) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p y)
    (α : (HomotopyCategory.mk x : hoFunctor.obj E) ⟶ HomotopyCategory.mk y)
    (hα : IsIso ((hoFunctor.map p).toFunctor.map α)) : IsIso α := by
  let P := (hoFunctor.map p).toFunctor
  have : IsIso (P.map α) := hα
  obtain ⟨β, hβ⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.hoFunctorMap_bijective_of_initialBoundary p y x hy).2 (inv (P.map α))
  refine ⟨⟨β, ?_, ?_⟩⟩
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.hoFunctorMap_bijective_of_initialBoundary p x x hx).1
    change P.map (α ≫ β) = P.map (𝟙 _)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, hβ]
    exact IsIso.hom_inv_id (P.map α)
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.hoFunctorMap_bijective_of_initialBoundary p y y hy).1
    change P.map (β ≫ α) = P.map (𝟙 _)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, hβ]
    exact IsIso.inv_hom_id (P.map α)

/-- 概要：底で可換な三辺を、普遍な始点間の可逆な比較射で閉じる。
方針：指定した底の同型を Hom 全射性で持ち上げ、残りの可換性を単射性で示す。
規約：第三・第四の頂点には普遍性を要求しない。
使われ方：局所 Kan 輸送の比較正方形。 -/
lemma exists_kanInitialBoundaryHom_comparison {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) (x y z w : E _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p x) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p y)
    (e : (HomotopyCategory.mk x : hoFunctor.obj E) ⟶ HomotopyCategory.mk z)
    (f : (HomotopyCategory.mk y : hoFunctor.obj E) ⟶ HomotopyCategory.mk w)
    (a : (HomotopyCategory.mk z : hoFunctor.obj E) ⟶ HomotopyCategory.mk w)
    (u : (hoFunctor.map p).toFunctor.obj (HomotopyCategory.mk x) ⟶
      (hoFunctor.map p).toFunctor.obj (HomotopyCategory.mk y)) (hu : IsIso u)
    (h : (hoFunctor.map p).toFunctor.map e ≫ (hoFunctor.map p).toFunctor.map a =
      u ≫ (hoFunctor.map p).toFunctor.map f) :
    ∃ m : (HomotopyCategory.mk x : hoFunctor.obj E) ⟶ HomotopyCategory.mk y,
      IsIso m ∧ (hoFunctor.map p).toFunctor.map m = u ∧ e ≫ a = m ≫ f := by
  obtain ⟨m, hm⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.hoFunctorMap_bijective_of_initialBoundary p x y hx).2 u
  have hi : IsIso ((hoFunctor.map p).toFunctor.map m) := hm.symm ▸ hu
  refine ⟨m, initialBoundaryHom_isIso_of_map p hx hy m hi, hm, ?_⟩
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.hoFunctorMap_bijective_of_initialBoundary p x w hx).1
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hm]
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
