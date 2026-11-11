module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanFamilies
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TerminalArrowRelative
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeTerminalBoundary

/-! # 共通の第一枝を持つ span の終対象枝の変更

概要：第一枝が同じで第二枝が終対象へ向かう二つの span は関手として同型である。
方針：始点評価の fiber 内で第二枝が終対象であることを使い、第一枝を固定して span の族へ写す。
規約：値域は quasicategory。使われ方：指定した零枝への cofiber の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：span 関手の頂点は二つの枝への制限で決まる。
方針：Yoneda で零単体からの射に直し、span の族の射の一意性を使う。
規約：値域の仮定は不要。使われ方：固定枝の族の両端の同定。 -/
lemma spanFunctorVertex_ext {X : SSet.{u}}
    {v w : ((ihom (horn 2 0 : SSet.{u})).obj X) _⦋0⦌}
    (hL : ((pre horn₂₀.ι₀₁).app X).app (Opposite.op ⦋0⦌) v =
      ((pre horn₂₀.ι₀₁).app X).app (Opposite.op ⦋0⦌) w)
    (hR : ((pre horn₂₀.ι₀₂).app X).app (Opposite.op ⦋0⦌) v =
      ((pre horn₂₀.ι₀₂).app X).app (Opposite.op ⦋0⦌) w) : v = w := by
  apply SSet.yonedaEquiv.symm.injective
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamily_hom_ext
  · rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, hL]
  · rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, hR]

/-- 概要：第一枝が同じで第二枝の終点が終対象である二つの span は同型である。
方針：始点を固定した辺の fiber の終対象の一意性を、固定第一枝と貼る族の射で送る。
規約：二つの終対象やそこへの辺は異なってよい。使われ方：零枝の選択の変更。 -/
lemma nonempty_functorIso_span_of_first_eq_terminal_second {X : SSet.{u}} [Quasicategory X]
    (F G : (horn 2 0 : SSet.{u}) ⟶ X) (hfirst : horn₂₀.ι₀₁ ≫ F = horn₂₀.ι₀₁ ≫ G)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((horn₂₀.ι₀₂ ≫ F).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((horn₂₀.ι₀₂ ≫ G).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  let f := horn₂₀.ι₀₁ ≫ F
  let x := f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  have hsource (H : (horn 2 0 : SSet.{u}) ⟶ X) :
      (horn₂₀.ι₀₂ ≫ H).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        (horn₂₀.ι₀₁ ≫ H).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    rfl
  have hxF : p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₂ ≫ F)) = x := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
    exact hsource F
  have hxG : p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₂ ≫ G)) = x := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, hsource G, ← hfirst]
  let a : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₂ ≫ F), by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]; exact hxF⟩
  let b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₂ ≫ G), by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]; exact hxG⟩
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex a := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting.isTerminalVertex_fiber p x a
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalBoundaryLifting_arrowSource_of_terminalTarget _ hF)
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex b := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting.isTerminalVertex_fiber p x b
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalBoundaryLifting_arrowSource_of_terminalTarget _ hG)
  let L : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x ⟶ (ihom (Δ[1] : SSet.{u})).obj X := SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p x
  have hLR : L ≫ p = R ≫ p := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp]
    change SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) ≫ p = SSet.const x
    rw [SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  let T := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows L R hLR
  have hTa : T.app (Opposite.op ⦋0⦌) a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F := by
    apply spanFunctorVertex_ext
    · have h := ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_left L R hLR) (Opposite.op ⦋0⦌)) a
      exact h
    · have h := ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_right L R hLR) (Opposite.op ⦋0⦌)) a
      exact h
  have hTb : T.app (Opposite.op ⦋0⦌) b = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G := by
    apply spanFunctorVertex_ext
    · have h := ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_left L R hLR) (Opposite.op ⦋0⦌)) b
      change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₁ ≫ G)
      rw [← hfirst]
      exact h
    · have h := ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_right L R hLR) (Opposite.op ⦋0⦌)) b
      exact h
  let a' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) : SSet.{u}) _⦋0⦌ := ⟨a, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    simpa only [hα, op_id, CategoryTheory.Functor.map_id_apply] using ha⟩
  let b' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) : SSet.{u}) _⦋0⦌ := ⟨b, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    simpa only [hα, op_id, CategoryTheory.Functor.map_id_apply] using hb⟩
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices_isContractibleKan (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x) ⟨a, ha⟩
  have := hc.kanComplex
  let S := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p x)).ι ≫ T
  have hSa : S.app (Opposite.op ⦋0⦌) a' = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F := hTa
  have hSb : S.app (Opposite.op ⦋0⦌) b' = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G := hTb
  exact ⟨(eqToIso (congrArg SSet.HomotopyCategory.mk hSa)).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (hc.isTerminalVertex a') (hc.isTerminalVertex b')) S ≪≫
      eqToIso (congrArg SSet.HomotopyCategory.mk hSb)⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
