module

public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.PrismFilling

/-!
概要：関手の同型に沿った境界充填の移送。
方針：境界の可逆なホモトピーと一方の充填を prism 上で貼り合わせる。
規約：単なる頂点ごとの同型ではなく関手単体集合の同型を使う。
使われ方：Kerodon §4.5.1、§4.8.4 の同値による充填の保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：prism の先頭を交換すると標準的なホモトピーの先頭。
方針：積の二成分を入れ替える。
規約：時刻零の端点。
使われ方：Kerodon §4.8.4 の境界のホモトピーの向き。 -/
lemma prismEndpoint_zero_braiding (A : SSet.{u}) :
    prismEndpoint 0 A ≫ (β_ (Δ[1] : SSet.{u}) A).hom = SSet.ι₀ := rfl

/-- 概要：prism の終端を交換すると標準的なホモトピーの終端。
方針：積の二成分を入れ替える。
規約：時刻一の端点。
使われ方：Kerodon §4.8.4 の境界のホモトピーの向き。 -/
lemma prismEndpoint_one_braiding (A : SSet.{u}) :
    prismEndpoint 1 A ≫ (β_ (Δ[1] : SSet.{u}) A).hom = SSet.ι₁ := rfl

/-- 概要：境界からの同型な二射の一方が充填できれば他方も充填できる。
方針：同型のホモトピーを境界の prism に置き、可逆な最初の垂直辺で全体を延長する。
規約：標的を quasicategory とする。
使われ方：Kerodon §4.8.4 の同値による終対象と極限の保存。 -/
lemma FunctorIso.exists_boundaryFilling {Y : SSet.{u}} [Quasicategory Y] {n : ℕ}
    {f g : (boundary n : SSet.{u}) ⟶ Y} (e : FunctorIso f g)
    (hf : ∃ F : (Δ[n] : SSet.{u}) ⟶ Y, (boundary n).ι ≫ F = f) :
    ∃ G : (Δ[n] : SSet.{u}) ⟶ Y, (boundary n).ι ≫ G = g := by
  obtain ⟨F₀, hF₀⟩ := hf
  cases n with
  | zero => exact ⟨F₀, boundary.hom_ext₀⟩
  | succ n =>
    let H := FunctorIso.simplicialHomotopy e
    let T := boundary.{u} (n + 1)
    let S := horn.{u} 1 0
    let H' := (β_ (Δ[1] : SSet.{u}) (T : SSet.{u})).hom ≫ H.h
    have hH₀ : prismEndpoint 0 (T : SSet.{u}) ≫ H' = f := by
      rw [← Category.assoc, prismEndpoint_zero_braiding]
      exact H.h₀
    have hH₁ : prismEndpoint 1 (T : SSet.{u}) ≫ H' = g := by
      rw [← Category.assoc, prismEndpoint_one_braiding]
      exact H.h₁
    let q := Subcomplex.unionProd.isPushout S T
    have hw : (S.ι ▷ (T : SSet.{u})) ≫ H' =
        ((S : SSet.{u}) ◁ T.ι) ≫ (snd (S : SSet.{u}) Δ[n + 1] ≫ F₀) := by
      rw [hornOneFirst_prism_factorization, Category.assoc, hH₀, ← hF₀]
      rfl
    let a := q.desc H' (snd (S : SSet.{u}) Δ[n + 1] ≫ F₀) hw
    have ha₁ : Subcomplex.unionProd.ι₁ S T ≫ a = H' := q.inl_desc _ _ _
    let x : (T : SSet.{u}) _⦋0⦌ :=
      ⟨stdSimplex.obj₀Equiv.symm 0, vertex_mem_boundary n 0⟩
    let v : ((Δ[1] : SSet.{u}) ⊗ (T : SSet.{u})) _⦋1⦌ :=
      ⟨homotopyIntervalEdge.edge, (SSet.Truncated.Edge.id (X := (truncation 2).obj T) x).edge⟩
    have hv : (Subcomplex.unionProd.ι₁ S T).app (Opposite.op ⦋1⦌) v =
        ⟨prismFirstVerticalEdge (n + 1), prismFirstVerticalEdge_mem n⟩ := by
      apply Subtype.ext
      apply Prod.ext
      · apply stdSimplex.ext
        intro i
        fin_cases i <;> rfl
      · change T.ι.app (Opposite.op ⦋1⦌)
          (SSet.Truncated.Edge.id (X := (truncation 2).obj T) x).edge =
            PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) 1
        rw [← pinchedConstant_one]
        exact pinchedConstant_map T.ι x 1
    have hedge : a.app (Opposite.op ⦋1⦌)
        ⟨prismFirstVerticalEdge (n + 1), prismFirstVerticalEdge_mem n⟩ =
          (simplicialHomotopyVertexEdge H x).edge := by
      have h := ConcreteCategory.congr_hom (NatTrans.congr_app ha₁ (Opposite.op ⦋1⦌)) v
      change a.app (Opposite.op ⦋1⦌)
        ((Subcomplex.unionProd.ι₁ S T).app (Opposite.op ⦋1⦌) v) =
          H'.app (Opposite.op ⦋1⦌) v at h
      rw [hv] at h
      exact h
    have he : IsInvertibleEdge (edgeOfSimplex (a.app (Opposite.op ⦋1⦌)
        ⟨prismFirstVerticalEdge (n + 1), prismFirstVerticalEdge_mem n⟩)) :=
      (isInvertibleEdge_congr hedge).mpr
        (simplicialHomotopyOfFunctorEdge_vertex_isInvertible
          (FunctorIso.edge e) (FunctorIso.edge_isInvertible e) x)
    obtain ⟨F, hF⟩ := prism_exists_extension_of_invertible_firstEdge n a he
    have hFH : (Δ[1] ◁ T.ι) ≫ F = H' := by
      rw [← Subcomplex.unionProd.ι₁_ι S T, Category.assoc, hF, ha₁]
    refine ⟨prismEndpoint 1 Δ[n + 1] ≫ F, ?_⟩
    rw [← Category.assoc, ← prismEndpoint_naturality, Category.assoc, hFH, hH₁]

/-- 概要：境界からの同型な二射の充填の存在は同値。
方針：同型と逆同型に沿って境界充填を移す。
規約：同型は境界を始域とする関手単体集合で取る。
使われ方：Kerodon §4.8.4 の充填条件の同型不変性。 -/
lemma FunctorIso.boundaryFilling_iff {Y : SSet.{u}} [Quasicategory Y] {n : ℕ}
    {f g : (boundary n : SSet.{u}) ⟶ Y} (e : FunctorIso f g) :
    (∃ F : (Δ[n] : SSet.{u}) ⟶ Y, (boundary n).ι ≫ F = f) ↔
      (∃ G : (Δ[n] : SSet.{u}) ⟶ Y, (boundary n).ι ≫ G = g) :=
  ⟨FunctorIso.exists_boundaryFilling e, FunctorIso.exists_boundaryFilling e.symm⟩

end SerrePositivity.InfinityCategories
