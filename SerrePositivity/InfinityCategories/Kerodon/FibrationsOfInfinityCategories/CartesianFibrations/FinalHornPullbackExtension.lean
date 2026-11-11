module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FinalHornInverseImage
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange

/-!
概要：最後の外ホーンの任意の pullback 表示に図式の延長を移す。
方針：逆像部分複体との標準同型を通し、辺の像と境界の等式を保持する。
規約：可逆化条件は実際の全空間の cocartesian 辺について述べる。
使われ方：相対指数のホーン持ち上げの図式表示への適用。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：任意の pullback 四角形で元の cocartesian 辺の持ち上げは cocartesian。
方針：元の射でホーンを充填し、pullback の普遍性で新しい底へ戻す。
規約：元の射の fibration 性を追加で要求しない。
使われ方：終端辺の逆像での可逆化条件の照合。 -/
lemma isCocartesianEdge_isPullback {P E A B : SSet.{u}}
    {i : P ⟶ E} {a : P ⟶ A} {p : E ⟶ B} {f : A ⟶ B}
    (hs : IsPullback i a p f) (e : P _⦋1⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (i.app (Opposite.op ⦋1⦌) e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge a e := by
  intro n t b ht sq
  let sq' : CommSq (t ≫ i) (horn (n + 2) 0).ι p (b ≫ f) :=
    ⟨by rw [Category.assoc, hs.w, ← Category.assoc, sq.w, Category.assoc]⟩
  have := he n (t ≫ i) (b ≫ f)
    (by change i.app _ (t.app _ _) = _; rw [ht]) sq'
  refine CommSq.HasLift.mk' {
    l := hs.lift sq'.lift b sq'.fac_right
    fac_left := ?_
    fac_right := hs.lift_snd _ _ _ }
  apply hs.hom_ext
  · rw [Category.assoc, hs.lift_fst]
    exact sq'.fac_left
  · rw [Category.assoc, hs.lift_snd]
    exact sq.w.symm

/-- 概要：任意の pullback 表示で最後の外ホーン上の可逆化する図式を延長できる。
方針：逆像部分複体へ同型で移し、実際の辺の等式で可逆化条件を戻す。
規約：全ての境界条件は射の厳密な等式。
使われ方：相対指数の cartesian 性を判定する外ホーンの図式の延長。 -/
lemma exists_kanFinalHornPullback_extension (n : ℕ) {P E D : SSet.{u}}
    [Quasicategory D] (p : E ⟶ (Δ[n + 2] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (i : P ⟶ E) (a : P ⟶ (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}))
    (hs : IsPullback i a p (horn (n + 2) (Fin.last (n + 2))).ι) (H : P ⟶ D)
    (he : ∀ s : P _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (i.app (Opposite.op ⦋1⦌) s) →
      p.app (Opposite.op ⦋1⦌) (i.app (Opposite.op ⦋1⦌) s) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n).val →
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌) s))) :
    ∃ G : E ⟶ D, i ≫ G = H := by
  let A := horn.{u} (n + 2) (Fin.last (n + 2))
  let hA := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.subcomplexInverseImage_isPullback p A).flip
  let e := hs.isoPullback ≪≫ hA.isoPullback.symm
  have hi : e.hom ≫ (A.preimage p).ι = i := by
    dsimp only [e]
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      IsPullback.isoPullback_inv_fst, IsPullback.isoPullback_hom_fst]
  have hi' : e.inv ≫ i = (A.preimage p).ι := by
    rw [← hi, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨G, hG⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanFinalHornInverseImage_extension n p (e.inv ≫ H) (by
    intro s hs hb
    have hv : i.app (Opposite.op ⦋1⦌) (e.inv.app (Opposite.op ⦋1⦌) s) = s.val :=
      congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) s) hi'
    exact he (e.inv.app _ s) (by rw [hv]; exact hs) (by rw [hv]; exact hb))
  refine ⟨G, ?_⟩
  rw [← hi, Category.assoc, hG, ← Category.assoc, e.hom_inv_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
