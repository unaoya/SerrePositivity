module

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorRelativeInitial
public import SerrePositivity.InfinityCategories.Core.CocartesianPrismBoundary

/-!
概要：指定した部分パラメータを固定して、点ごとの相対始対象・終対象から境界の族を充填する。
方針：境界の族と指定部分上の族を積の和で貼り、相対骨格の始点または終点で充填する。
規約：射の fibration 性・単体集合の quasicategory 性を追加しない。
使われ方：Kerodon §7.1.8 の相対充填を用いる Kan 拡張の制限写像の証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対始対象で始まる境界の族は、部分パラメータ上の指定充填を保って充填できる。
方針：K×境界と A×単体の和へ貼り、境界外の時間単体の始点が零であることを使う。
規約：A は任意の部分単体集合。自然な族の存在を結論として構成する。
使われ方：点ごとの相対余極限の持ち上げを部分図式に相対的な形へ移す。 -/
lemma kanInitialBoundaryFamily_lift_relative {K X Y : SSet.{u}}
    (p : X ⟶ Y) (A : K.Subcomplex) (n : ℕ) (f : K ⟶ X)
    (b : (boundary (n + 1) : SSet.{u}) ⟶ (ihom K).obj X)
    (a : (A : SSet.{u}) ⊗ (Δ[n + 1] : SSet.{u}) ⟶ X)
    (g : K ⊗ (Δ[n + 1] : SSet.{u}) ⟶ Y)
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (functorVertex f))
    (hba : (A.ι ▷ (boundary (n + 1) : SSet.{u})) ≫ uncurry b =
      ((A : SSet.{u}) ◁ (boundary (n + 1)).ι) ≫ a)
    (hbp : uncurry b ≫ p = (K ◁ (boundary (n + 1)).ι) ≫ g)
    (hap : a ≫ p = (A.ι ▷ (Δ[n + 1] : SSet.{u})) ≫ g)
    (hf : ∀ k : K _⦋0⦌, InitialBoundaryLifting p (f.app (Opposite.op ⦋0⦌) k)) :
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
    have h := vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v.2)
    rw [Equiv.symm_apply_apply] at h
    exact h
  have hup : u ≫ p = U.ι ≫ g := by
    apply q.hom_ext
    · rw [← Category.assoc, hu₁, hbp, ← Category.assoc, Subcomplex.unionProd.ι₁_ι]
    · rw [← Category.assoc, hu₂, hap, ← Category.assoc, Subcomplex.unionProd.ι₂_ι]
  have hbfirst : b.app (Opposite.op ⦋0⦌)
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n _⟩ =
      functorVertex f := by
    apply SSet.yonedaEquiv.symm.injective
    simpa only [boundaryVertex, SSet.yonedaEquiv_symm_comp] using hb
  have ht : ∀ (m : ℕ) (s : (K ⊗ (Δ[n + 1] : SSet.{u})) _⦋m + 1⦌),
      s ∉ U.obj (Opposite.op ⦋m + 1⦌) →
      InitialBoundaryLifting p (u.app (Opposite.op ⦋0⦌) ⟨simplexFirstVertex s, hU _⟩) := by
    intro m s hs
    have hs₂ : s.2 ∉ T.obj (Opposite.op ⦋m + 1⦌) :=
      fun h ↦ hs (Or.inl ⟨by trivial, h⟩)
    have he₂ := simplexFirstVertex_stdSimplex_of_notMem_boundary s.2 hs₂
    have hv := ConcreteCategory.congr_hom (NatTrans.congr_app hu₁ (Opposite.op ⦋0⦌))
      (show (K ⊗ (T : SSet.{u})) _⦋0⦌ from
        (simplexFirstVertex s.1,
          ⟨simplexFirstVertex (A := (Δ[n + 1] : SSet.{u})) s.2,
            by rw [he₂]; exact vertex_mem_boundary n 0⟩))
    change u.app (Opposite.op ⦋0⦌) ⟨(simplexFirstVertex s.1, simplexFirstVertex s.2), _⟩ =
      (uncurry b).app (Opposite.op ⦋0⦌)
        (simplexFirstVertex s.1, ⟨simplexFirstVertex s.2, _⟩) at hv
    rw [simplexFirstVertex_prod, hv]
    simp only [he₂]
    change InitialBoundaryLifting p ((b.app (Opposite.op ⦋0⦌)
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), _⟩).app
        (Opposite.op ⦋0⦌) (𝟙 _) (simplexFirstVertex s.1))
    rw [hbfirst]
    exact hf _
  obtain ⟨F, hF, hFp⟩ := exists_lift_of_initial_first_vertices U hU p u g hup ht
  refine ⟨F, ?_, ?_, hFp⟩
  · rw [← Subcomplex.unionProd.ι₁_ι A T, Category.assoc, hF, hu₁]
  · rw [← Subcomplex.unionProd.ι₂_ι A T, Category.assoc, hF, hu₂]

/-- 概要：相対終対象で始まる境界の族は、部分パラメータ上の指定充填を保って充填できる。
方針：K×境界と A×単体の和へ貼り、境界外の時間単体の終点が最後の頂点であることを使う。
規約：A は任意の部分単体集合。自然な族の存在を結論として構成する。
使われ方：点ごとの相対極限の持ち上げを部分図式に相対的な形へ移す。 -/
lemma kanTerminalBoundaryFamily_lift_relative {K X Y : SSet.{u}}
    (p : X ⟶ Y) (A : K.Subcomplex) (n : ℕ) (f : K ⟶ X)
    (b : (boundary (n + 1) : SSet.{u}) ⟶ (ihom K).obj X)
    (a : (A : SSet.{u}) ⊗ (Δ[n + 1] : SSet.{u}) ⟶ X)
    (g : K ⊗ (Δ[n + 1] : SSet.{u}) ⟶ Y)
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b = SSet.yonedaEquiv.symm (functorVertex f))
    (hba : (A.ι ▷ (boundary (n + 1) : SSet.{u})) ≫ uncurry b =
      ((A : SSet.{u}) ◁ (boundary (n + 1)).ι) ≫ a)
    (hbp : uncurry b ≫ p = (K ◁ (boundary (n + 1)).ι) ≫ g)
    (hap : a ≫ p = (A.ι ▷ (Δ[n + 1] : SSet.{u})) ≫ g)
    (hf : ∀ k : K _⦋0⦌, TerminalBoundaryLifting p (f.app (Opposite.op ⦋0⦌) k)) :
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
    have h := vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v.2)
    rw [Equiv.symm_apply_apply] at h
    exact h
  have hup : u ≫ p = U.ι ≫ g := by
    apply q.hom_ext
    · rw [← Category.assoc, hu₁, hbp, ← Category.assoc, Subcomplex.unionProd.ι₁_ι]
    · rw [← Category.assoc, hu₂, hap, ← Category.assoc, Subcomplex.unionProd.ι₂_ι]
  have hblast : b.app (Opposite.op ⦋0⦌)
      ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1) : Fin (n + 2)), vertex_mem_boundary n _⟩ =
      functorVertex f := by
    apply SSet.yonedaEquiv.symm.injective
    simpa only [boundaryVertex, SSet.yonedaEquiv_symm_comp] using hb
  have ht : ∀ (m : ℕ) (s : (K ⊗ (Δ[n + 1] : SSet.{u})) _⦋m + 1⦌),
      s ∉ U.obj (Opposite.op ⦋m + 1⦌) →
      TerminalBoundaryLifting p (u.app (Opposite.op ⦋0⦌) ⟨simplexLastVertex s, hU _⟩) := by
    intro m s hs
    have hs₂ : s.2 ∉ T.obj (Opposite.op ⦋m + 1⦌) :=
      fun h ↦ hs (Or.inl ⟨by trivial, h⟩)
    have he₂ := simplexLastVertex_stdSimplex_of_notMem_boundary s.2 hs₂
    have hv := ConcreteCategory.congr_hom (NatTrans.congr_app hu₁ (Opposite.op ⦋0⦌))
      (show (K ⊗ (T : SSet.{u})) _⦋0⦌ from
        (simplexLastVertex s.1,
          ⟨simplexLastVertex (B := (Δ[n + 1] : SSet.{u})) s.2,
            by rw [he₂]; exact vertex_mem_boundary n (Fin.last (n + 1))⟩))
    change u.app (Opposite.op ⦋0⦌) ⟨(simplexLastVertex s.1, simplexLastVertex s.2), _⟩ =
      (uncurry b).app (Opposite.op ⦋0⦌)
        (simplexLastVertex s.1, ⟨simplexLastVertex s.2, _⟩) at hv
    rw [simplexLastVertex_prod, hv]
    simp only [he₂]
    change TerminalBoundaryLifting p ((b.app (Opposite.op ⦋0⦌)
      ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1) : Fin (n + 2)), _⟩).app
        (Opposite.op ⦋0⦌) (𝟙 _) (simplexLastVertex s.1))
    rw [hblast]
    exact hf _
  obtain ⟨F, hF, hFp⟩ := exists_lift_of_terminal_last_vertices U hU p u g hup ht
  refine ⟨F, ?_, ?_, hFp⟩
  · rw [← Subcomplex.unionProd.ι₁_ι A T, Category.assoc, hF, hu₁]
  · rw [← Subcomplex.unionProd.ι₂_ι A T, Category.assoc, hF, hu₂]

end SerrePositivity.InfinityCategories
