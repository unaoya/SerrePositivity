module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianTransportStrictification
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PullbackCartesianPair

/-!
概要：共通の底上の引き戻しの cartesian fibration 性。
方針：第二成分を輸送し、その像へ第一成分の輸送を厳密に持ち上げて合わせる。
規約：第一成分からの射は inner fibration で、各 fiber で可逆辺を持ち上げる。
使われ方：全空間の相対 Kan 比較の標的の cartesian な輸送。

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

/-- 概要：cartesian な輸送を保つ二つの射の引き戻しも底上の cartesian fibration となる。
方針：第二成分の輸送の像を第一成分へ厳密に持ち上げ、引き戻しの辺の判定を使う。
規約：第一成分の射の各 fiber で終点指定の可逆辺の持ち上げを要求する。
使われ方：相対 Kan 拡張の局所普遍性を全空間へ移す標的の構造。 -/
lemma cartesianFibration_pullback_over {X Y Z C : SSet.{u}}
    [Quasicategory X] [Quasicategory Z] [Quasicategory C]
    (p : X ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p] (q : Y ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration q]
    (r : Z ⟶ C) [InnerFibration r] (f : X ⟶ Z) [InnerFibration f] (g : Y ⟶ Z)
    (hf : f ≫ r = p) (hg : g ≫ r = q)
    (hpresf : ∀ e : X _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p e →
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge r (f.app (Opposite.op ⦋1⦌) e))
    (hpresg : ∀ e : Y _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge q e →
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge r (g.app (Opposite.op ⦋1⦌) e))
    (hlift : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleTargetLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p r f hf c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration (pullback.fst f g ≫ p) where
  mem := by
    refine ⟨?_, ?_⟩
    · have : InnerFibration (pullback.snd f g) :=
        ⟨innerFibrations.pullback_snd _ _ (InnerFibration.mem (q := f))⟩
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pullbackOver_snd_projection p q r f g hf hg]
      exact innerFibrations.comp_mem _ _ (InnerFibration.mem (q := pullback.snd f g))
        (InnerFibration.mem (q := q))
    · intro x b hb
      let x₁ := (pullback.fst f g).app (Opposite.op ⦋0⦌) x
      let x₂ := (pullback.snd f g).app (Opposite.op ⦋0⦌) x
      have hqx : q.app (Opposite.op ⦋0⦌) x₂ =
          (pullback.fst f g ≫ p).app (Opposite.op ⦋0⦌) x :=
        ConcreteCategory.congr_hom (NatTrans.congr_app
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pullbackOver_snd_projection p q r f g hf hg) (Opposite.op ⦋0⦌)) x
      obtain ⟨v, hvt, hvq, hvc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration.mem (p := q) |>.2 x₂ b
        (hb.trans (congrArg SSet.yonedaEquiv.symm hqx.symm))
      have hfx : f.app (Opposite.op ⦋0⦌) x₁ = g.app (Opposite.op ⦋0⦌) x₂ :=
        ConcreteCategory.congr_hom (NatTrans.congr_app (pullback.condition (f := f) (g := g))
          (Opposite.op ⦋0⦌)) x
      have hvgt : stdSimplex.δ (0 : Fin 2) ≫ (v ≫ g) =
          SSet.yonedaEquiv.symm (f.app (Opposite.op ⦋0⦌) x₁) := by
        rw [← Category.assoc, hvt, SSet.yonedaEquiv_symm_comp, ← hfx]
      have hvgc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge r (SSet.yonedaEquiv (v ≫ g)) := by
        rw [SSet.yonedaEquiv_comp]
        exact hpresg _ hvc
      obtain ⟨u, hut, huf, huc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanCartesianTransport_over_cartesianEdge p r f hf
        hpresf hlift x₁ (v ≫ g) hvgc hvgt
      let a := pullback.lift u v huf
      have haf : a ≫ pullback.fst f g = u := pullback.lift_fst _ _ _
      have hag : a ≫ pullback.snd f g = v := pullback.lift_snd _ _ _
      refine ⟨a, ?_, ?_, ?_⟩
      · apply pullback.hom_ext
        · rw [Category.assoc, haf, hut, SSet.yonedaEquiv_symm_comp]
        · rw [Category.assoc, hag, hvt, SSet.yonedaEquiv_symm_comp]
      · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pullbackOver_snd_projection p q r f g hf hg, ← Category.assoc, hag, hvq]
      · apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_pullback_over p q r f g hf hg (SSet.yonedaEquiv a)
        · rw [← SSet.yonedaEquiv_comp, haf]
          exact huc
        · rw [← SSet.yonedaEquiv_comp, hag]
          exact hvc
        · rw [← SSet.yonedaEquiv_comp, haf]
          exact hpresf _ huc

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
