module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SimplexVertexDetection
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
概要：prism の境界と先頭を貼り合わせる補題。
方針：部分複体の積の和の pushout と、頂点での標準単体への射の一意性を使う。
規約：正次元の標準単体の全頂点は境界に属する。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の右ファイブレーション版。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：先頭の一次ホーンの prism への包含は先頭の端点を経由する。
方針：ホーンの全単体が零に定値であることを頂点ごとに使う。
規約：Λ[1,0] は時刻零の端点。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の先頭の貼り合わせ。 -/
lemma hornOneFirst_prism_factorization (A : SSet.{u}) :
    ((horn 1 0).ι ▷ A) = snd (horn 1 0 : SSet.{u}) A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, b⟩
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    obtain ⟨j, hj, hm⟩ := (mem_horn_iff_notMem_range a.val (0 : Fin 2)).1 a.property
    have hjv : j.val ≠ 0 := by intro h; exact hj (Fin.ext h)
    have hj1 : j = 1 := Fin.ext (by change j.val = 1; have := j.isLt; omega)
    subst j
    have hv : (a.val i).val ≠ 1 := by
      intro h
      exact hm ⟨i, Fin.ext h⟩
    apply Fin.ext
    change (a.val i).val = 0
    have := (a.val i).isLt
    omega
  · rfl

/-- 概要：正次元の prism の全頂点は境界の prism に属する。
方針：第二成分の頂点が標準単体の境界に属する。
規約：先頭と境界の和の部分複体を使う。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の base の一意性。 -/
lemma prismDomain_contains_vertices (n : ℕ)
    (v : ((Δ[1] : SSet.{u}) ⊗ Δ[n + 1]) _⦋0⦌) :
    v ∈ (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).obj (Opposite.op ⦋0⦌) := by
  rw [Subcomplex.mem_unionProd_iff]
  left
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary.{u} n (stdSimplex.obj₀Equiv.{u} v.2)
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- 概要：prism の境界と先頭を固定した延長は base の収縮と可換。
方針：部分複体が全頂点を含むので標準単体への射の頂点による一意性を使う。
規約：延長を相対的に選び直す必要はない。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の絶対的なホーン充填から相対的な充填への移行。 -/
lemma prism_extension_comp {E : SSet.{u}} (n : ℕ) (p : E ⟶ (Δ[n + 1] : SSet.{u}))
    (a : (Subcomplex.unionProd (horn 1 0) (boundary (n + 1)) : SSet.{u}) ⟶ E)
    (ha : a ≫ p = (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstContraction (n + 1))
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ E)
    (hF : (Subcomplex.unionProd (horn 1 0) (boundary (n + 1))).ι ≫ F = a) :
    F ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstContraction (n + 1) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_of_subcomplex_vertices _ (prismDomain_contains_vertices n)
  rw [← Category.assoc, hF, ha]

/-- 概要：最初の fiber が可縮な右ファイブレーションでは正次元の標準単体の境界を持ち上げられる。
方針：境界を最初の fiber へ移しそこで充填し、prism 全体へ延長して元の端点を制限する。
規約：base の射は標準単体の恒等射。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の右ファイブレーション版。 -/
lemma rightFibration_fillBoundary_over_stdSimplex_succ {E : SSet.{u}} (n : ℕ)
    (p : E ⟶ (Δ[n + 1] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p]
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm 0)))
    (b : (boundary (n + 1) : SSet.{u}) ⟶ E) (hb : b ≫ p = (boundary (n + 1)).ι) :
    ∃ f : (Δ[n + 1] : SSet.{u}) ⟶ E, (boundary (n + 1)).ι ≫ f = b ∧ f ≫ p = 𝟙 _ := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  obtain ⟨H, hH₁, hH⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_liftBoundaryPrism p b hb
  obtain ⟨F₀, hF₀, hF₀p⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.boundaryPrism_fillZero p H hH hc
  let S := horn.{u} 1 0
  let T := boundary.{u} (n + 1)
  let q := Subcomplex.unionProd.isPushout S T
  have hw : (S.ι ▷ (T : SSet.{u})) ≫ H =
      ((S : SSet.{u}) ◁ T.ι) ≫ (snd (S : SSet.{u}) Δ[n + 1] ≫ F₀) := by
    rw [hornOneFirst_prism_factorization, Category.assoc, ← hF₀]
    rfl
  let a := q.desc H (snd (S : SSet.{u}) Δ[n + 1] ≫ F₀) hw
  have ha₁ : Subcomplex.unionProd.ι₁ S T ≫ a = H := q.inl_desc _ _ _
  have ha₂ : Subcomplex.unionProd.ι₂ S T ≫ a =
      snd (S : SSet.{u}) Δ[n + 1] ≫ F₀ := q.inr_desc _ _ _
  have hap : a ≫ p = (Subcomplex.unionProd S T).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstContraction (n + 1) := by
    apply q.hom_ext
    · rw [← Category.assoc, ha₁, hH, ← Category.assoc, Subcomplex.unionProd.ι₁_ι]
    · rw [← Category.assoc, ha₂, Category.assoc, hF₀p,
        ← Category.assoc, Subcomplex.unionProd.ι₂_ι,
        hornOneFirst_prism_factorization, Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstContraction_zero, SSet.comp_const]
  let s := a.app (Opposite.op ⦋1⦌)
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge (n + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge_mem n⟩
  have hs : p.app (Opposite.op ⦋1⦌) s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) 1 := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hap (Opposite.op ⦋1⦌))
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge (n + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge_mem n⟩
    exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge_contraction (n + 1))
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_isInvertibleEdge_of_constant_image p
    (stdSimplex.obj₀Equiv.symm 0) s hs
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prism_exists_extension_of_invertible_firstEdge n a he
  have hFp := prism_extension_comp n p a hap F hF
  have hFH : (Δ[1] ◁ T.ι) ≫ F = H := by
    rw [← Subcomplex.unionProd.ι₁_ι S T, Category.assoc, hF, ha₁]
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[n + 1] ≫ F, ?_, ?_⟩
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hFH, hH₁]
  · rw [Category.assoc, hFp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstContraction_one]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
