module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.NerveInclusionSimplex

/-! # 閉零圏の nerve から dg nerve への包含

概要：通常の nerve の各辺を閉零射として読み、高次成分を零にする単体的写像。
方針：単調写像に沿う成分の引き戻しを照合する。
規約：零・一単体は N1 の同値と整合する。使われ方：通常の関手から導来 ∞ 関手を作る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

private theorem closedNerveHom_map_of_eq {n : ℕ}
    (F : ComposableArrows (_root_.SerrePositivity.DifferentialGraded.ClosedCategory A D) n) {a b : Fin (n + 1)}
    (hab : a = b) (hle : a ≤ b) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (F.map (homOfLE hle)) 0)
      (_root_.SerrePositivity.DifferentialGraded.unitElement A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (F.obj b))).val := by
  subst b
  change HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (F.map (𝟙 a)) 0) _
  rw [F.map_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_id]

/-- 概要：閉零射の列の dg 単体化は単調写像による引き戻しと整合する。
方針：単射成分・潰れた辺・高次零成分の三つの場合を調べる。
規約：通常の nerve の退化も含む。使われ方：nerve 包含の自然性。 -/
theorem closedNerveSimplex_pullback {m n : ℕ}
    (F : ComposableArrows (_root_.SerrePositivity.DifferentialGraded.ClosedCategory A D) n) (α : Fin (m + 1) →o Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (α.monotone.functor ⋙ F) = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex F).pullback α := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext rfl ?_
  apply heq_of_eq
  funext I a b k hI ha hb hk
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveData (α.monotone.functor ⋙ F)).hom I a b k hI ha hb hk =
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveData F).pullback α).hom I a b k hI ha hb hk
  by_cases hi : Set.InjOn α (I : Set (Fin (m + 1)))
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
    rfl
  · by_cases hc : I.card = 2
    · have hk0 : k = 0 := by omega
      subst hk0
      have hamin : IsLeast (I : Set (Fin (m + 1))) a := by rw [ha]; exact I.isLeast_min' _
      have hbmax : IsGreatest (I : Set (Fin (m + 1))) b := by rw [hb]; exact I.isGreatest_max' _
      have hab := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.collapse_two hi hc hamin hbmax
      have hl := closedNerveHom_map_of_eq F hab (α.monotone (hamin.2 hbmax.1))
      have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_collapsed_pair
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveData F) α I a b 0 hI ha hb hk hi hc
      exact eq_of_heq (hl.trans hr.symm)
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc]
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne _ k (by omega)

variable (A D)

/-- 概要：閉零圏の通常の nerve から dg nerve への標準射。
方針：閉零射の列を高次成分零の単体へ送り、引き戻しの整合性を使う。
規約：対象宇宙と Hom 宇宙は独立。使われ方：離散代数の導来 ∞ 圏への埋め込み。 -/
def closedNerveInclusion : nerve (ClosedCategory A D) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D where
  app Δ := ↾fun F => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex F
  naturality _ _ f := by
    ext F
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex_pullback F f.unop.toOrderHom

/-- 概要：通常の nerve 包含は零単体の対象を保つ。
方針：N1 の頂点同値と構成の対象成分を評価する。
規約：閉零圏の包装を外す。使われ方：埋め込みの対象の同定。 -/
theorem closedNerveInclusion_vertex (F : (nerve (_root_.SerrePositivity.DifferentialGraded.ClosedCategory A D)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A D ((closedNerveInclusion A D).app _ F) =
      ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (nerveEquiv F) := rfl

/-- 概要：通常の nerve 包含の一単体は元の閉零射に対応する。
方針：唯一の辺の成分を次数零で評価する。
規約：N1 の辺同値との整合性。使われ方：辺が誘導する射の計算。 -/
theorem closedNerveInclusion_edge (F : (nerve (_root_.SerrePositivity.DifferentialGraded.ClosedCategory A D)) _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.edgeEquiv A D ((closedNerveInclusion A D).app _ F) =
      ⟨fun i => ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (F.obj i),
        _root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D (F.obj 0) (F.obj 1) (F.map (homOfLE (by decide)))⟩ := by
  apply Sigma.ext rfl
  apply heq_of_eq
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero _

/-- 概要：通常の nerve 包含の高次成分は零である。
方針：三点以上なら成分次数が負になることを使う。
規約：任意の単体と三点以上の部分集合。使われ方：厳密な合成列の高次データ。 -/
theorem closedNerveInclusion_higher {n : ℕ}
    (F : (nerve (_root_.SerrePositivity.DifferentialGraded.ClosedCategory A D)) _⦋n⦌) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hthree : 3 ≤ I.card) :
    (((closedNerveInclusion A D).app _ F) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n).hom I a b k hI ha hb hk = 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne _ k (by omega)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
