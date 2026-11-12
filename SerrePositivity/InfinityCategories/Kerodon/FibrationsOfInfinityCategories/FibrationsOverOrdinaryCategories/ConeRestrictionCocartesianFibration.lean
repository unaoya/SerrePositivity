module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ConeHomotopyTransport

/-!
概要：錐の制限は cocartesian fibration。
方針：基底の関手の辺を錐の頂点を固定して持ち上げ、その頂点での可逆性から cocartesian 性を得る。
規約：添字は任意、値域は quasicategory。
使われ方：Kerodon Corollary 5.3.7.5（Tag 02VW）・7.1.6.13（Tag 02XB）、関手 ∞ 圏の極限。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：錐全体から図式への制限射は cocartesian fibration。
方針：始点を指定した基底の辺を頂点を固定した錐のホモトピーで持ち上げ、頂点で可逆な辺のホーン充填を使う。
規約：X は quasicategory、K は任意。
使われ方：Kerodon Corollary 5.3.7.5（Tag 02VW）・7.1.6.13（Tag 02XB） の極限錐の相対終対象への接続。 -/
instance cocartesianHornFibration_coneRestriction (K X : SSet.{u}) [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) where
  toInnerFibration := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction
    infer_instance
  exists_lift v b a := by
    let D := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K
    let F₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv D X).symm v
    have hF₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F₀ = v := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv D X).apply_symm_apply v
    let sBase : ((ihom K).obj X) _⦋1⦌ := a.edge
    let H : K ⊗ (Δ[1] : SSet.{u}) ⟶ X := uncurry (SSet.yonedaEquiv.symm sBase)
    have h₀ : SSet.ι₀ ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K ≫ F₀ := by
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
      have hs : ((ihom K).obj X).δ 1 sBase =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X).app (Opposite.op ⦋0⦌) v := a.src_eq
      have hz := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_uncurry_zero sBase
      refine hz.trans (hs.trans ?_)
      rw [← hF₀]
      rfl
    obtain ⟨G, hG₀, hGr, hGl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneHomotopy_extend F₀ H h₀
    let s := SSet.yonedaEquiv (curry G)
    have hs₀ : ((ihom D).obj X).δ 1 s = v := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_uncurry_zero]
      dsimp [s]
      rw [Equiv.symm_apply_apply, uncurry_curry, hG₀, hF₀]
    let e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom D).obj X)) v
        (((ihom D).obj X).δ 0 s) :=
      { edge := s
        src_eq := hs₀
        tgt_eq := rfl }
    have hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X).app (Opposite.op ⦋1⦌) e.edge = a.edge := by
      have h : curry G ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K)).app X =
          SSet.yonedaEquiv.symm sBase := by
        apply uncurry_injective
        rw [uncurry_pre_app, uncurry_curry]
        exact hGr
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry G)) = a.edge
      rw [← SSet.yonedaEquiv_comp]
      change SSet.yonedaEquiv (curry G ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K)).app X) = sBase
      rw [h, Equiv.apply_symm_apply]
    have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation K X))) := by
      let apex := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
      let z := F₀.app (Opposite.op ⦋0⦌) apex
      have heq : (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation K X))).edge =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z 1 := by
        let w : ((Δ[0] : SSet.{u}) ⊗ Δ[1]) _⦋1⦌ :=
          ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1,
            SSet.yonedaEquiv (𝟙 Δ[1])⟩
        have hh := ConcreteCategory.congr_hom (NatTrans.congr_app hGl (Opposite.op ⦋1⦌)) w
        change G.app (Opposite.op ⦋1⦌)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋1⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1),
              SSet.yonedaEquiv (𝟙 Δ[1])) =
          F₀.app (Opposite.op ⦋1⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋1⦌)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1)) at hh
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map] at hh
        exact hh
      have hinv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isEquivalencePathVertex_const z
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex at hinv
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex] at hinv
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr heq).2 hinv
    exact ⟨_, e, hp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.hasCocartesianHornLifting_coneRestriction_of_apex e hi⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
