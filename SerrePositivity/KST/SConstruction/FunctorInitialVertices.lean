module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorInitialBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorTerminal
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed
public import Mathlib.Tactic.CrossRefAttribute

/-! # 関手圏の点ごとの始対象と零対象
概要：全ての点で始対象・零対象となる関手頂点の普遍性を証明する。
方針：初めの頂点による相対骨格の境界充填と A6 の終対象側を使う。
規約：周囲の quasicategory 性は不要。使われ方：cofiber 族の零角の普遍性。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：各頂点で始対象となる関手は関手 ∞ 圏でも始対象。
方針：境界の uncurry を直積上で延長し、新しい単体の始点には点ごとの始対象性を使う。
規約：この向きには標的の quasicategory 性を必要としない。
使われ方：HTT 5.1.2.2、Kerodon Corollary 7.1.8.15（Tag 02XP） の空図式の場合の双対。 -/
@[kerodon 02XP]
lemma isInitialVertex_functorVertex_of_pointwise {K X : SSet.{u}} (f : K ⟶ X)
    (hf : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (f.app (Opposite.op ⦋0⦌) k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := by
  intro n b hb
  let A : (K ⊗ (Δ[n + 1] : SSet.{u})).Subcomplex :=
    (⊤ : K.Subcomplex).prod (boundary (n + 1))
  let e : (A : SSet.{u}) ≅ K ⊗ (boundary (n + 1) : SSet.{u}) :=
    Subcomplex.prodIso ⊤ (boundary (n + 1)) ≪≫
      whiskerRightIso (Subcomplex.topIso K) (boundary (n + 1) : SSet.{u})
  let a : (A : SSet.{u}) ⟶ X := e.hom ≫ uncurry b
  have hA : ∀ v : (K ⊗ (Δ[n + 1] : SSet.{u})) _⦋0⦌,
      v ∈ A.obj (Opposite.op ⦋0⦌) := by
    intro v
    refine ⟨by trivial, ?_⟩
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v.2)
    rw [Equiv.symm_apply_apply] at h
    exact h
  have hbfirst : b.app (Opposite.op ⦋0⦌)
      ⟨stdSimplex.obj₀Equiv.symm (0), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n _⟩ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f := by
    apply SSet.yonedaEquiv.symm.injective
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex, SSet.yonedaEquiv_symm_comp] using hb
  have ht : ∀ (m : ℕ) (s : (K ⊗ (Δ[n + 1] : SSet.{u})) _⦋m + 1⦌),
      s ∉ A.obj (Opposite.op ⦋m + 1⦌) →
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s, hA _⟩) := by
    intro m s hs
    have hs₂ : s.2 ∉ (boundary (n + 1)).obj (Opposite.op ⦋m + 1⦌) :=
      fun h ↦ hs ⟨by trivial, h⟩
    have he₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexFirstVertex_stdSimplex_of_notMem_boundary s.2 hs₂
    have ha : a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s, hA _⟩ =
        f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s.1) := by
      change (uncurry b).app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s).1, ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s).2, _⟩) = _
      rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_simplexFirstVertex_prod]
      simp only [he₂]
      change (b.app (Opposite.op ⦋0⦌)
        ⟨stdSimplex.obj₀Equiv.symm (0), _⟩).app
          (Opposite.op ⦋0⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s.1) = _
      rw [hbfirst]
      rfl
    rw [ha]
    exact hf _
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stable_exists_extension_of_initial_first_vertices A hA a ht
  refine ⟨curry F, ?_⟩
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry]
  have he : e.inv ≫ A.ι = K ◁ (boundary (n + 1)).ι := by
    apply SSet.hom_ext
    rintro ⟨⟨d⟩⟩
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [← he, Category.assoc, hF]
  simp only [a, Iso.inv_hom_id_assoc]


/-- 概要：各点で零対象となる関手は関手単体集合でも零対象。
方針：始対象性と A6 の終対象性を合わせる。
規約：K と X は任意。使われ方：cofiber の族の零頂点。 -/
lemma isZeroVertex_functorVertex_of_pointwise {K X : SSet.{u}} (f : K ⟶ X)
    (hf : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (f.app (Opposite.op ⦋0⦌) k)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) :=
  ⟨isInitialVertex_functorVertex_of_pointwise f (fun k ↦ (hf k).1),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise f (fun k ↦ (hf k).2)⟩

/-- 概要：関手頂点の全評価が零対象ならその頂点は零対象。
方針：関手頂点を実際の射で表示し、点ごとの零対象判定を使う。
規約：追加の存在条件は不要。使われ方：点ごとの零角を関手圏へ移す。 -/
lemma isZeroVertex_of_pointwise {K X : SSet.{u}} (v : ((ihom K).obj X) _⦋0⦌)
    (hv : ∀ k : K _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app (Opposite.op ⦋0⦌) v)) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex v := by
  obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K X).surjective v
  apply isZeroVertex_functorVertex_of_pointwise f
  intro k
  have h := hv k
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) at h
  rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at h

end SerrePositivity.KST.SConstruction
