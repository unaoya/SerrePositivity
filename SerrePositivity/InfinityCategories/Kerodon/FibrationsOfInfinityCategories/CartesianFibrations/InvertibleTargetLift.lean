module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.RelativeEquivalencePathAt
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-!
概要：相対可逆 path の充填性から終点指定の可逆辺の持ち上げを抽出する。
方針：可逆辺を path の頂点とし、指定終点との引き戻しの頂点を持ち上げる。
規約：可逆辺と終点は厳密に保存する。
使われ方：相対 Kan 比較の標的の二つの輸送の像を一致させる。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：相対可逆 path の全境界充填から可逆 path の頂点の持ち上げを得る。
方針：指定端点と標的の path を引き戻しへ合わせ、相対写像の切断を使う。
規約：j は始点または終点。
使われ方：可逆辺の終点を指定した厳密な持ち上げ。 -/
lemma exists_kanEquivalencePathVertex_lift {E B : SSet.{u}} (p : E ⟶ B) (j : Fin 2)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p j)]
    (x : E _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath B) _⦋0⦌)
    (hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B j).app (Opposite.op ⦋0⦌) v =
      p.app (Opposite.op ⦋0⦌) x) :
    ∃ w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath E) _⦋0⦌,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap p).app (Opposite.op ⦋0⦌) w = v ∧
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint E j).app (Opposite.op ⦋0⦌) w = x := by
  let a := SSet.yonedaEquiv.symm v
  let b := SSet.yonedaEquiv.symm x
  have hab : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B j = b ≫ p := by
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, hv]
  let t := pullback.lift a b hab
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p j)
  let l := t ≫ s
  have hl : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p j = t := by
    rw [Category.assoc, hs]
    exact Category.comp_id t
  refine ⟨SSet.yonedaEquiv l, ?_, ?_⟩
  · have h : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap p = a := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_fst p j, ← Category.assoc, hl]
      exact pullback.lift_fst _ _ _
    have h' := congrArg SSet.yonedaEquiv h
    simpa only [a, b, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h'
  · have h : l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint E j = b := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_snd p j, ← Category.assoc, hl]
      exact pullback.lift_snd _ _ _
    have h' := congrArg SSet.yonedaEquiv h
    simpa only [a, b, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h'

/-- 概要：相対可逆 path の充填性を持つ射では可逆辺を終点指定で持ち上げられる。
方針：可逆辺の path 頂点を持ち上げ、対応する区間からの射に戻す。
規約：辺の像と終点はホモトピー類でなく厳密に指定する。
使われ方：cartesian 輸送の比較三角形の最初の辺の持ち上げ。 -/
lemma exists_kanInvertibleEdge_lift_target {E B : SSet.{u}} (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p 1)]
    (x : E _⦋0⦌) (e : (Δ[1] : SSet.{u}) ⟶ B)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv e)))
    (ht : stdSimplex.δ (0 : Fin 2) ≫ e = SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x)) :
    ∃ l : (Δ[1] : SSet.{u}) ⟶ E,
      stdSimplex.δ (0 : Fin 2) ≫ l = SSet.yonedaEquiv.symm x ∧ l ≫ p = e ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv l)) := by
  let v := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv e)) he
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1).app (Opposite.op ⦋0⦌) v =
      p.app (Opposite.op ⦋0⦌) x := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathVertex_one]
    have h := congrArg SSet.yonedaEquiv ht
    simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using h
  obtain ⟨w, hwp, hwt⟩ := exists_kanEquivalencePathVertex_lift p 1 x v hv
  obtain ⟨l, hl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] E).surjective w.val
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex w
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex w.val at hi
  rw [← hl] at hi
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex l) at hi
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex] at hi
  refine ⟨l, ?_, ?_, hi⟩
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)).app (Opposite.op ⦋0⦌) w.val = x at hwt
    rw [← hl, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at hwt
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    have hvalue : l.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1) =
        E.δ 0 (SSet.yonedaEquiv l) := by
      rw [← SSet.yonedaEquiv.symm_apply_apply l, SSet.yonedaEquiv_symm_app,
        Equiv.apply_symm_apply]
      have hv : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
          SimplexCategory.δ (0 : Fin 2) := by decide
      rw [hv]
      rfl
    exact hvalue.symm.trans hwt
  · have h := congrArg Subtype.val hwp
    change ((ihom (Δ[1] : SSet.{u})).map p).app (Opposite.op ⦋0⦌) w.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (SSet.yonedaEquiv e)) at h
    rw [← hl, Equiv.symm_apply_apply] at h
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] B).injective h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
