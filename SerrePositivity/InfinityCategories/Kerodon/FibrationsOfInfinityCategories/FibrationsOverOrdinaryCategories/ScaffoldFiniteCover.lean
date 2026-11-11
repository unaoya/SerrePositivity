module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteTail
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementAssembly

/-!
概要：有限順序上の simplicial replacement の最初の係数部分と末尾による被覆。
方針：射列が零から始まる場合は始点の係数単体を保ち、それ以外は末尾へ因子化する。
規約：被覆は各次数の集合として述べ、係数の充填性は要求しない。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、Theorem 5.3.5.7（Tag 037Q）、pushout 分解の全射性。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：有限順序上の simplicial replacement は末尾と最初の係数部分で被覆される。
方針：底の射列の始点が零かどうかで分け、始点評価の恒等性または末尾への因子化を使う。
規約：各次数で二つの射の像の和が全体となる。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、pushout 分解の共同全射性。 -/
lemma scaffoldFiniteReplacement_cover (n : ℕ)
    (F : ULift.{u} (Fin (n + 2)) ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementBaseMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n) F).app d) ⊔
      Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialAssembly F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1))).app d) =
        Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨σ, τ⟩
  change (∃ x, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementBaseMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n) F).app d x = ⟨σ, τ⟩) ∨
    ∃ x, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialAssembly F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1))).app d x = ⟨σ, τ⟩
  by_cases h : (σ.obj 0).down = 0
  · right
    have hσ : σ.obj 0 = ULift.up (0 : Fin (n + 2)) := ULift.ext h
    let v := τ ≫ F.map (eqToHom hσ)
    refine ⟨(σ, SSet.yonedaEquiv v), ?_⟩
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    change SSet.yonedaEquiv.symm (SSet.yonedaEquiv v) ≫
      F.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1)).to (σ.obj 0)) = τ
    rw [Equiv.symm_apply_apply]
    dsimp only [v]
    have hc : eqToHom hσ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 1)).to (σ.obj 0) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [Category.assoc, ← F.map_comp, hc, F.map_id, Category.comp_id]
  · left
    obtain ⟨δ, hδ⟩ : ∃ δ, δ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n = σ :=
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTailFactor σ, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTailFactor_comp σ h⟩
    subst σ
    exact ⟨⟨δ, τ⟩, rfl⟩

/-- 概要：末尾の直積部分の像に含まれない単体の底の射列は零から始まる。
方針：零から始まらない射列の末尾への因子化で像の中の表示を作り、矛盾を得る。
規約：係数の単体集合 K は任意。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、貼り合わせ部分の外で係数を復元する条件。 -/
lemma scaffoldFiniteTail_complement_zero (n : ℕ) (K : SSet.{u})
    (d : SimplexCategoryᵒᵖ) (s : (nerve (ULift.{u} (Fin (n + 2))) ⊗ K).obj d)
    (hs : s ∉ Set.range ((nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n) ▷ K).app d)) :
    (s.1.obj 0).down = 0 := by
  by_contra h
  obtain ⟨δ, hδ⟩ : ∃ δ, δ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n = s.1 :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTailFactor s.1, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTailFactor_comp s.1 h⟩
  exact hs ⟨(δ, s.2), Prod.ext hδ rfl⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
