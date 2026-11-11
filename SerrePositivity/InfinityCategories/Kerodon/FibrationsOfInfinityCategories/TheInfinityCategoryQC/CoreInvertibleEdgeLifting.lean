module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.QuasicategoryCore
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleTargetLiftingIso

/-!
概要：可逆辺の終点指定の持ち上げを core の一次右ホーンの持ち上げにする。
方針：ホーンの唯一の点を頂点に戻し、可逆な lift の一単体を core に入れる。
規約：元の辺と終点を厳密に保つ。元の関手に inner fibration 性はまだ要求しない。
使われ方：core の右ファイブレーション性の一次元の場合。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：終点指定で可逆辺を持ち上げられる関手の core は一次右ホーンを持ち上げる。
方針：唯一の頂点を Yoneda で読み、可逆辺の lift を core の一単体へ戻す。
規約：始域・終域の quasicategory 性はこの段階には不要。
使われ方：core の Kan fibration 性に必要な頂点指定の辺の持ち上げ。 -/
lemma coreMap_liftHorn_one_last {X Y : SSet.{u}}
    (p : X ⟶ Y) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleTargetLifting p)
    (a : (horn 1 1 : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X : SSet.{u}))
    (b : (Δ[1] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y : SSet.{u}))
    (sq : CommSq a (horn 1 1).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap p) b) :
    ∃ l : (Δ[1] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X : SSet.{u}),
      (horn 1 1).ι ≫ l = a ∧ l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap p = b := by
  let x := SSet.yonedaEquiv (horn.ι (1 : Fin 2) 0 (by decide) ≫ a)
  have ht : stdSimplex.δ (0 : Fin 2) ≫ b =
      SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap p).app (Opposite.op ⦋0⦌) x) := by
    rw [← horn.ι_ι_assoc (1 : Fin 2) 0 (by decide), ← sq.w,
      ← Category.assoc, ← SSet.yonedaEquiv_symm_comp]
    exact congrArg (fun f ↦ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap p)
      (SSet.yonedaEquiv.symm_apply_apply (horn.ι (1 : Fin 2) 0 (by decide) ≫ a)).symm
  have htraw : stdSimplex.δ (0 : Fin 2) ≫ (b ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).ι) =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x.val) := by
    rw [← Category.assoc, ht, SSet.yonedaEquiv_symm_comp]
    rfl
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (b ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).ι))) := by
    rw [SSet.yonedaEquiv_comp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge (SSet.yonedaEquiv b)
  obtain ⟨l, hlt, hlp, hl⟩ := hp x.val (b ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).ι) hb htraw
  let lc : (Δ[1] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X : SSet.{u}) :=
    SSet.yonedaEquiv.symm ⟨SSet.yonedaEquiv l, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_mem_edge_iff _).mpr hl⟩
  have hlc : lc ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι = l := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    change (SSet.yonedaEquiv lc).val = _
    rw [Equiv.apply_symm_apply]
  refine ⟨lc, ?_, ?_⟩
  · apply horn.hom_ext'
    intro j hj
    fin_cases j
    · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι).mp
      rw [horn.ι_ι_assoc, Category.assoc, hlc]
      change stdSimplex.δ (0 : Fin 2) ≫ l =
        (horn.ι (1 : Fin 2) 0 (by decide) ≫ a) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι
      rw [hlt]
      have hx := SSet.yonedaEquiv.symm_apply_apply (horn.ι (1 : Fin 2) 0 (by decide) ≫ a)
      exact congrArg (fun f ↦ f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore X).ι) hx
    · exact (hj rfl).elim
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore Y).ι).mp
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι, ← Category.assoc, hlc, hlp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
