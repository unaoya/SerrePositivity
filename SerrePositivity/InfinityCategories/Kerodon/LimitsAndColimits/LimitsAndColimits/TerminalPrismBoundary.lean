module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorTerminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrismBoundaryExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismFilling
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalExtension

/-! # 終対象を終点に持つ prism の境界延長

概要：境界上で終点が終対象である prism は、始点の指定を保って延長できる。
方針：始点と境界の和を相対骨格で延長し、新しい単体の終点が区間の最後にあることを使う。
規約：標的の quasicategory 性は不要。
使われ方：S3 の零対象へ向かう辺と span の族の構成。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：区間の始点ホーンの外の単体の最後の頂点は時刻一。
方針：値一が現れなければ始点ホーンに属し、単調性で最後の値を決める。
規約：次数は任意。
使われ方：終対象を持つ prism の相対骨格の充填。 -/
lemma stable_interval_lastVertex_of_notMem_firstHorn {n : ℕ}
    (s : (Δ[1] : SSet.{u}) _⦋n⦌)
    (hs : s ∉ (horn 1 0).obj (Opposite.op ⦋n⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s = stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
  have hr : (1 : Fin 2) ∈ Set.range s := by
    by_contra h
    exact hs ((mem_horn_iff_notMem_range s 0).2 ⟨1, by decide, h⟩)
  obtain ⟨j, hj⟩ := hr
  apply stdSimplex.obj₀Equiv.injective
  change s (Fin.last n) = 1
  apply le_antisymm (Fin.le_last _)
  change (1 : Fin 2) ≤ _
  rw [← hj]
  exact (stdSimplex.asOrderHom s).monotone (Fin.le_last j)

/-- 概要：境界上の終点が終対象である prism は始点を固定して延長できる。
方針：始点ホーンと境界の積を貼り、新しい単体の最後の頂点の終対象性で相対骨格を充填する。
規約：n+1 次元の境界を扱う。quasicategory 性は不要。
使われ方：S3 の零対象に向かう辺の族の持ち上げ。 -/
lemma stable_prism_extend_terminal_boundary {X : SSet.{u}} (n : ℕ)
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary (n + 1) : SSet.{u}) ⟶ X)
    (F₀ : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (hF₀ : (boundary (n + 1)).ι ≫ F₀ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (boundary (n + 1) : SSet.{u}) ≫ H)
    (ht : ∀ v : (boundary (n + 1) : SSet.{u}) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (H.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2), v))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ X,
      (Δ[1] ◁ (boundary (n + 1)).ι) ≫ F = H ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n + 1] ≫ F = F₀ := by
  let S := horn.{u} 1 0
  let T := boundary.{u} (n + 1)
  let q := Subcomplex.unionProd.isPushout S T
  have hw : (S.ι ▷ (T : SSet.{u})) ≫ H =
      ((S : SSet.{u}) ◁ T.ι) ≫ (snd (S : SSet.{u}) Δ[n + 1] ≫ F₀) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneFirst_prism_factorization, Category.assoc, ← hF₀]
    rfl
  let a := q.desc H (snd (S : SSet.{u}) Δ[n + 1] ≫ F₀) hw
  have ha₁ : Subcomplex.unionProd.ι₁ S T ≫ a = H := q.inl_desc _ _ _
  have ha₂ : Subcomplex.unionProd.ι₂ S T ≫ a =
      snd (S : SSet.{u}) Δ[n + 1] ≫ F₀ := q.inr_desc _ _ _
  let A := Subcomplex.unionProd S T
  have hA : ∀ v : ((Δ[1] : SSet.{u}) ⊗ Δ[n + 1]) _⦋0⦌,
      v ∈ A.obj (Opposite.op ⦋0⦌) := by
    intro v
    apply Or.inl
    refine ⟨by trivial, ?_⟩
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v.2)
    rw [Equiv.symm_apply_apply] at h
    exact h
  have hterm : ∀ (m : ℕ) (s : ((Δ[1] : SSet.{u}) ⊗ Δ[n + 1]) _⦋m + 1⦌),
      s ∉ A.obj (Opposite.op ⦋m + 1⦌) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s, hA _⟩) := by
    intro m s hs
    have hs₁ : s.1 ∉ S.obj (Opposite.op ⦋m + 1⦌) := fun h ↦ hs (Or.inr ⟨h, by trivial⟩)
    have hv₁ := stable_interval_lastVertex_of_notMem_firstHorn s.1 hs₁
    let v : (T : SSet.{u}) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s.2, by
      have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s.2))
      rw [Equiv.symm_apply_apply] at h
      exact h⟩
    let w : ((Δ[1] : SSet.{u}) ⊗ (T : SSet.{u})) _⦋0⦌ :=
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2), v)
    have hh := ConcreteCategory.congr_hom (NatTrans.congr_app ha₁ (Opposite.op ⦋0⦌)) w
    have he : a.app (Opposite.op ⦋0⦌) ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s, hA _⟩ =
        H.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2), v) := by
      change a.app (Opposite.op ⦋0⦌)
        ⟨(stdSimplex.obj₀Equiv.symm (1 : Fin 2), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s.2), _⟩ =
          H.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2), v) at hh
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex_prod, hv₁]
      exact hh
    rw [he]
    exact ht v
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_extension_of_terminal_last_vertices A hA a hterm
  refine ⟨F, ?_, ?_⟩
  · rw [← Subcomplex.unionProd.ι₁_ι S T, Category.assoc, hF, ha₁]
  · have h : (S.ι ▷ (Δ[n + 1] : SSet.{u})) ≫ F =
        snd (S : SSet.{u}) Δ[n + 1] ≫ F₀ := by
      rw [← Subcomplex.unionProd.ι₂_ι S T, Category.assoc, hF, ha₂]
    have h' := congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection (Δ[n + 1] : SSet.{u}) ≫ f) h
    dsimp only [S] at h'
    simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.hornOneFirstSection_snd,
      Category.id_comp] using h'

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
