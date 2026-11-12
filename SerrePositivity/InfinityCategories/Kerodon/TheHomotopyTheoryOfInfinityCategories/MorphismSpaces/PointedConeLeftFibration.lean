module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PointedConeHornLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ConeHomotopyTransport

/-!
概要：固定頂点からの錐の制限射の left fibration 性。
方針：一次元は頂点固定の輸送を使い、二次元以上は内外のホーン充填を合わせる。
規約：安定性や有限極限を仮定しない。使われ方：一般安定性判定の全錐比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 先頭の一次ホーンの全単体はその唯一の頂点の定値単体。 -/
lemma hornOneFirst_simplex_constant (n : ℕ) (t : (horn 1 0 : SSet.{u}) _⦋n⦌) :
    t = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstVertex n := by
  apply Subtype.ext
  let w : ((horn 1 0 : SSet.{u}) ⊗ Δ[0]) _⦋n⦌ :=
    ⟨t, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n⟩
  have hh := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneFirst_prism_factorization (Δ[0] : SSet.{u}))
      (Opposite.op ⦋n⦌)) w
  exact congrArg Prod.fst hh

/-- 頂点を厳密に固定した図式の辺を指定錐から持ち上げる。 -/
lemma pointedCone_oneHorn_lift {K X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) (a : (horn 1 0 : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeFamily K X x)
    (β : (Δ[1] : SSet.{u}) ⟶ (ihom K).obj X)
    (hw : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection K X x = (horn 1 0).ι ≫ β) :
    ∃ F : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeFamily K X x,
      (horn 1 0).ι ≫ F = a ∧ F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection K X x = β := by
  let D := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K
  let v := a.app (Opposite.op ⦋0⦌) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstVertex
  let F₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv D X).symm v.val
  have hF₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F₀ = v.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv D X).apply_symm_apply v.val
  let H := uncurry β
  have h₀ : SSet.ι₀ ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K ≫ F₀ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
    have hh := ConcreteCategory.congr_hom (NatTrans.congr_app hw (Opposite.op ⦋0⦌))
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstVertex
    have hz := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_uncurry_zero (SSet.yonedaEquiv β)
    rw [Equiv.symm_apply_apply] at hz
    rw [hz]
    change ((ihom K).obj X).δ 1 (SSet.yonedaEquiv β) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F₀)
    rw [hF₀]
    have hn := ConcreteCategory.congr_hom
      (β.naturality (SimplexCategory.δ (1 : Fin 2)).op) (SSet.yonedaEquiv (𝟙 Δ[1]))
    change (β.app (Opposite.op ⦋0⦌))
      ((Δ[1] : SSet.{u}).δ 1 (SSet.yonedaEquiv (𝟙 Δ[1]))) =
        ((ihom K).obj X).δ 1 (β.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 Δ[1]))) at hn
    rw [← SSet.yonedaEquiv_comp, Category.id_comp] at hn
    have hpoint : (Δ[1] : SSet.{u}).δ 1 (SSet.yonedaEquiv (𝟙 Δ[1])) =
        (horn 1 0).ι.app (Opposite.op ⦋0⦌) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstVertex := by
      apply stdSimplex.ext
      intro j
      fin_cases j
      rfl
    rw [hpoint] at hn
    exact hn.symm.trans hh.symm
  obtain ⟨G, hG₀, hGr, hGl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneHomotopy_extend F₀ H h₀
  have hzero : F₀.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = x := by
    have hv := v.property
    rw [← hF₀, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at hv
    exact hv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero x)
  have hFx : curry G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation K X = SSet.const x := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro t
    let w : ((Δ[0] : SSet.{u}) ⊗ Δ[1]) _⦋n⦌ :=
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n, t⟩
    have hz := ConcreteCategory.congr_hom (NatTrans.congr_app hGl (Opposite.op ⦋n⦌)) w
    change G.app (Opposite.op ⦋n⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋n⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n), t) =
      F₀.app (Opposite.op ⦋n⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋n⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) n)) at hz
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, hzero] at hz
    change (uncurry (curry G)).app (Opposite.op ⦋n⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) n, t) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x n
    rw [uncurry_curry]
    exact hz
  have hFk : curry G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X = β := by
    apply uncurry_injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction, uncurry_pre_app, uncurry_curry]
    exact hGr
  have hFa : (horn 1 0).ι ≫ curry G = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation K X) x := by
    have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.ι₀ ≫ G) = v.val := by rw [hG₀, hF₀]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro t
    rw [hornOneFirst_simplex_constant n t]
    change (curry G).app (Opposite.op ⦋n⦌)
      ((horn 1 0).ι.app (Opposite.op ⦋n⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstVertex n)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
    congr 1
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ x (curry G) hFx, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation K X) x
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    exact hFa
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ x (curry G) hFx ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    exact hFk
/-- 固定頂点からの全錐の底への制限は左ファイブレーション。 -/
instance pointedConeProjection_leftFibration (K X : SSet.{u}) [Quasicategory X]
    (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedConeProjection K X x) where
  mem := by
    intro A B f hf
    cases hf with
    | @intro n i hi =>
      constructor
      intro a b sq
      cases n with
      | zero =>
        have hi₀ : i = 0 := Fin.ext (by change i.val = 0; change i.val < 1 at hi; omega)
        subst i
        obtain ⟨F, hFa, hFb⟩ := pointedCone_oneHorn_lift x a b sq.w
        exact CommSq.HasLift.mk' { l := F, fac_left := hFa, fac_right := hFb }
      | succ m =>
        by_cases hi₀ : i = 0
        · subst i
          obtain ⟨F, hFa, hFb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCone_initialHorn_lift x m a b sq.w
          exact CommSq.HasLift.mk' { l := F, fac_left := hFa, fac_right := hFb }
        · obtain ⟨F, hFa, hFb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCone_innerHorn_lift x m i
            (Fin.pos_iff_ne_zero.mpr hi₀) hi a b sq.w
          exact CommSq.HasLift.mk' { l := F, fac_left := hFa, fac_right := hFb }
end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
