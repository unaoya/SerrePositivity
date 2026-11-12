module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalCarrierBound

/-!
概要：元の境界と一致する最後の部分複体内の充填は、鎖を実現する空間へ持ち上がる。
方針：境界内の各非全射な制限を実際の境界写像で比較する。
規約：元の充填と元の鎖を成分として厳密に保持する。
使われ方：射影の境界持ち上げ性と全鎖の整合的な実現。

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
variable {I : Type u} [Preorder I] {X : SSet.{u}}

/-- 標準単体からの元の写像を指定した単体で評価する公式。 -/
lemma simplexHom_app_eq_map {Y : SSet.{u}} {m n : SimplexCategory}
    (f : stdSimplex.obj n ⟶ Y) (α : m ⟶ n) :
    f.app _ (stdSimplex.objEquiv.symm α) = Y.map α.op (SSet.yonedaEquiv f) := by
  have hf : SSet.yonedaEquiv.symm (SSet.yonedaEquiv f) = f :=
    SSet.yonedaEquiv.symm_apply_apply f
  conv_lhs => rw [← hf, SSet.yonedaEquiv_symm_app_objEquiv_symm]

/-- 同じ境界と一致する正次元の充填は、全ての制限の条件を保持する。 -/
lemma terminalCarrierCondition_of_filler {A : I → X.Subcomplex} {z : I → X _⦋0⦌}
    {n : ℕ} (b : (boundary (n + 1) : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).toSSet)
    (F : (Δ[n + 1] : SSet.{u}) ⟶ X) (q : (Δ[n + 1] : SSet.{u}) ⟶ nerve I)
    (h : (boundary (n + 1)).ι ≫ lift F q = b ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).ι)
    (hx : SSet.yonedaEquiv F ∈
      (A ((SSet.yonedaEquiv q).obj (Fin.last (n + 1)))).obj _) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierCondition A z (SSet.yonedaEquiv F) (SSet.yonedaEquiv q) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierCondition_of_boundary A z hx
  intro m α hα
  let t : (boundary (n + 1) : SSet.{u}).obj (Opposite.op m) :=
    ⟨stdSimplex.objEquiv.symm α, hα⟩
  have he : (F.app _ t.val, q.app _ t.val) = (b.app _ t).val :=
    congrArg (fun a : (boundary (n + 1) : SSet.{u}) ⟶ X ⊗ nerve I => a.app _ t) h
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierCondition A z (F.app _ t.val) (q.app _ t.val) := by
    change (F.app _ t.val, q.app _ t.val) ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).obj _
    rw [he]
    exact (b.app _ t).property
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierCondition A z
    (F.app _ (stdSimplex.objEquiv.symm α)) (q.app _ (stdSimplex.objEquiv.symm α)) at hp
  rw [← simplexHom_app_eq_map F α, ← simplexHom_app_eq_map q α]
  exact hp

/-- 全条件を満たす同じ元の単体と鎖から、実際の持ち上げを作る。 -/
def terminalCarrierSimplex {A : I → X.Subcomplex} {z : I → X _⦋0⦌} {n : ℕ}
    (F : (Δ[n] : SSet.{u}) ⟶ X) (q : (Δ[n] : SSet.{u}) ⟶ nerve I)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierCondition A z (SSet.yonedaEquiv F) (SSet.yonedaEquiv q)) :
    (Δ[n] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).toSSet :=
  SSet.yonedaEquiv.symm ⟨(SSet.yonedaEquiv F, SSet.yonedaEquiv q), h⟩

/-- 同じ持ち上げの元の積への写像。 -/
lemma terminalCarrierSimplex_ι {A : I → X.Subcomplex} {z : I → X _⦋0⦌} {n : ℕ}
    (F : (Δ[n] : SSet.{u}) ⟶ X) (q : (Δ[n] : SSet.{u}) ⟶ nerve I)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierCondition A z (SSet.yonedaEquiv F) (SSet.yonedaEquiv q)) :
    terminalCarrierSimplex F q h ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).ι = lift F q := by
  apply SSet.yonedaEquiv.injective
  simp only [terminalCarrierSimplex, SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
  rfl

/-- 同じ持ち上げの射影は元の鎖。 -/
lemma terminalCarrierSimplex_projection {A : I → X.Subcomplex} {z : I → X _⦋0⦌} {n : ℕ}
    (F : (Δ[n] : SSet.{u}) ⟶ X) (q : (Δ[n] : SSet.{u}) ⟶ nerve I)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierCondition A z (SSet.yonedaEquiv F) (SSet.yonedaEquiv q)) :
    terminalCarrierSimplex F q h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection A z = q := by
  change _ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).ι ≫ snd _ _) = q
  rw [← Category.assoc, terminalCarrierSimplex_ι, lift_snd]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
