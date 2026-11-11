module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeBoundaryFamily

/-!
概要：指定部分の外の単体の始点だけに相対普遍性を課して境界の族を延長する。
方針：二つの指定部分の和の外にある単体は、両成分とも指定部分の外にあることを使う。
規約：全頂点での普遍性を仮定せず、相対骨格で使う始点だけを仮定する。
使われ方：標準単体の境界を固定する場合に、最初の頂点だけの条件へ還元する。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：相対境界の族は、指定部分の外の単体の始点の普遍性だけから充填できる。
方針：積の和の外の単体の始点を計算し、相対骨格による延長を使う。
規約：指定部分内の他の頂点に普遍性は要求しない。
使われ方：境界を固定した関手圏での局所相対余極限の構成。 -/
lemma kanInitialBoundaryFamily_lift_of_relative_first_vertices {K X Y : SSet.{u}}
    (p : X ⟶ Y) (A : K.Subcomplex) (n : ℕ) (f : K ⟶ X)
    (b : (boundary (n + 1) : SSet.{u}) ⟶ (ihom K).obj X)
    (a : (A : SSet.{u}) ⊗ (Δ[n + 1] : SSet.{u}) ⟶ X)
    (g : K ⊗ (Δ[n + 1] : SSet.{u}) ⟶ Y)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (hba : (A.ι ▷ (boundary (n + 1) : SSet.{u})) ≫ uncurry b =
      ((A : SSet.{u}) ◁ (boundary (n + 1)).ι) ≫ a)
    (hbp : uncurry b ≫ p = (K ◁ (boundary (n + 1)).ι) ≫ g)
    (hap : a ≫ p = (A.ι ▷ (Δ[n + 1] : SSet.{u})) ≫ g)
    (hf : ∀ (m : ℕ) (s : K _⦋m + 1⦌), s ∉ A.obj (Opposite.op ⦋m + 1⦌) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p (f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s))) :
    ∃ F : K ⊗ (Δ[n + 1] : SSet.{u}) ⟶ X,
      (K ◁ (boundary (n + 1)).ι) ≫ F = uncurry b ∧
      (A.ι ▷ (Δ[n + 1] : SSet.{u})) ≫ F = a ∧ F ≫ p = g := by
  let T := boundary.{u} (n + 1)
  let U := Subcomplex.unionProd A T
  let q := Subcomplex.unionProd.isPushout A T
  let u := q.desc (uncurry b) a hba
  have hu₁ : Subcomplex.unionProd.ι₁ A T ≫ u = uncurry b := q.inl_desc _ _ _
  have hu₂ : Subcomplex.unionProd.ι₂ A T ≫ u = a := q.inr_desc _ _ _
  have hU : ∀ v : (K ⊗ (Δ[n + 1] : SSet.{u})) _⦋0⦌,
      v ∈ U.obj (Opposite.op ⦋0⦌) := by
    intro v
    refine Or.inl ⟨by trivial, ?_⟩
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v.2)
    rw [Equiv.symm_apply_apply] at h
    exact h
  have hup : u ≫ p = U.ι ≫ g := by
    apply q.hom_ext
    · rw [← Category.assoc, hu₁, hbp, ← Category.assoc, Subcomplex.unionProd.ι₁_ι]
    · rw [← Category.assoc, hu₂, hap, ← Category.assoc, Subcomplex.unionProd.ι₂_ι]
  have hbfirst : b.app (Opposite.op ⦋0⦌)
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n _⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f := by
    apply SSet.yonedaEquiv.symm.injective
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex, SSet.yonedaEquiv_symm_comp] using hb
  have ht : ∀ (m : ℕ) (s : (K ⊗ (Δ[n + 1] : SSet.{u})) _⦋m + 1⦌),
      s ∉ U.obj (Opposite.op ⦋m + 1⦌) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p (u.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s, hU _⟩) := by
    intro m s hs
    have hs₁ : s.1 ∉ A.obj (Opposite.op ⦋m + 1⦌) :=
      fun h ↦ hs (Or.inr ⟨h, by trivial⟩)
    have hs₂ : s.2 ∉ T.obj (Opposite.op ⦋m + 1⦌) :=
      fun h ↦ hs (Or.inl ⟨by trivial, h⟩)
    have he₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorRelativeInitial.simplexFirstVertex_stdSimplex_of_notMem_boundary s.2 hs₂
    have hv := ConcreteCategory.congr_hom (NatTrans.congr_app hu₁ (Opposite.op ⦋0⦌))
      (show (K ⊗ (T : SSet.{u})) _⦋0⦌ from
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s.1,
          ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex (A := (Δ[n + 1] : SSet.{u})) s.2,
            by rw [he₂]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩))
    change u.app (Opposite.op ⦋0⦌) ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s.1, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s.2), _⟩ =
      (uncurry b).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s.1, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s.2, _⟩) at hv
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorRelativeInitial.simplexFirstVertex_prod, hv]
    simp only [he₂]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p ((b.app (Opposite.op ⦋0⦌)
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), _⟩).app
        (Opposite.op ⦋0⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s.1))
    rw [hbfirst]
    exact hf m s.1 hs₁
  obtain ⟨F, hF, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.F1BFunctorCategoriesRelativeInitialExtension.exists_lift_of_initial_first_vertices U hU p u g hup ht
  refine ⟨F, ?_, ?_, hFp⟩
  · rw [← Subcomplex.unionProd.ι₁_ι A T, Category.assoc, hF, hu₁]
  · rw [← Subcomplex.unionProd.ι₂_ι A T, Category.assoc, hF, hu₂]


end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
