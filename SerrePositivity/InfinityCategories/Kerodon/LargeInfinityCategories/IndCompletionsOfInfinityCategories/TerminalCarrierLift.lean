module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalCarrier

/-!
概要：各単体の所属と指定頂点の等式から、元の図式を全鎖の実現空間へ持ち上げる。
方針：図式の自然性で全制限の条件を回収し、同じ積への写像を部分複体へ因子分解する。
規約：値写像と添字写像を厳密に保持する。
使われ方：coslice の有限余錐を、構成済み写像と比較できる実現空間内に戻す。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Preorder I] {X K : SSet.{u}}
  (A : I → X.Subcomplex) (z : I → X _⦋0⦌) (F : K ⟶ X) (q : K ⟶ nerve I)
  (hmem : ∀ (n : SimplexCategoryᵒᵖ) (s : K.obj n),
    F.app n s ∈ (A ((q.app n s).obj (Fin.last n.unop.len))).obj n)
  (hv : ∀ v : K _⦋0⦌, F.app _ v = z ((q.app _ v).obj 0))
include hmem hv

/-- 同じ図式の自然性により、全単体での条件から全ての制限の条件を回収する。 -/
lemma terminalCarrierCondition_of_local {n : SimplexCategory} (s : K.obj (Opposite.op n)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierCondition A z (F.app _ s) (q.app _ s) := by
  constructor
  · intro m α
    have hf := ConcreteCategory.congr_hom (F.naturality α.op) s
    have hq := ConcreteCategory.congr_hom (q.naturality α.op) s
    change F.app _ (K.map α.op s) = X.map α.op (F.app _ s) at hf
    change q.app _ (K.map α.op s) = (nerve I).map α.op (q.app _ s) at hq
    have hh := hmem _ (K.map α.op s)
    rw [hf, hq] at hh
    exact hh
  · intro i
    let α := (SimplexCategory.const ⦋0⦌ n i).op
    have hf := ConcreteCategory.congr_hom (F.naturality α) s
    have hq := ConcreteCategory.congr_hom (q.naturality α) s
    change F.app _ (K.map α s) = X.map α (F.app _ s) at hf
    change q.app _ (K.map α s) = (nerve I).map α (q.app _ s) at hq
    have hh := hv (K.map α s)
    rw [hf, hq] at hh
    exact hh

/-- 元の二つの図式を同じ実現空間内に持ち上げる。 -/
def terminalCarrierLift : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).toSSet :=
  Subcomplex.lift (lift F q) (by
    intro n y hy
    obtain ⟨s, rfl⟩ := hy
    exact terminalCarrierCondition_of_local A z F q hmem hv s)

/-- 元の積への包含は、同じ元の二成分を回収する。 -/
lemma terminalCarrierLift_ι :
    terminalCarrierLift A z F q hmem hv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).ι = lift F q :=
  Subcomplex.lift_ι _ _

/-- 同じ持ち上げの値は元の値写像。 -/
lemma terminalCarrierLift_value :
    terminalCarrierLift A z F q hmem hv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierValue A z = F := by
  change _ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).ι ≫ fst _ _) = F
  rw [← Category.assoc, terminalCarrierLift_ι, lift_fst]

/-- 同じ持ち上げの射影は元の添字写像。 -/
lemma terminalCarrierLift_projection :
    terminalCarrierLift A z F q hmem hv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection A z = q := by
  change _ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).ι ≫ snd _ _) = q
  rw [← Category.assoc, terminalCarrierLift_ι, lift_snd]

omit hmem hv in
/-- 同じ実現空間への写像は、元の値と添字の二成分で決まる。 -/
lemma terminalCarrier_hom_ext {f g : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).toSSet}
    (hvalue : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierValue A z = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierValue A z)
    (hproj : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection A z = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection A z) : f = g := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).ι).mp
  apply CartesianMonoidalCategory.hom_ext
  · exact hvalue
  · exact hproj

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
