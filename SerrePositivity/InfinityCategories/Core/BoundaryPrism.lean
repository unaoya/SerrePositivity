module

public import SerrePositivity.InfinityCategories.Core.PrismContraction
public import SerrePositivity.InfinityCategories.Core.VertexFiber

/-!
概要：右ファイブレーションの境界の先頭の fiber へのホモトピー。
方針：終端の端点の右 anodyne 性で標準単体の収縮を持ち上げる。
規約：base は標準単体、時刻一が元の境界。
使われ方：Kerodon Lemma 4.4.2.15 の右側の双対版。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右ファイブレーション上の境界を最初の fiber へホモトピーで移せる。
方針：最後の一次ホーンと境界の積の包含に対して持ち上げる。
規約：最後の端点は与えられた境界を厳密に再現する。
使われ方：Kerodon Lemma 4.4.2.15 の右ファイブレーション版の第一段階。 -/
lemma rightFibration_liftBoundaryPrism {E : SSet.{u}} {n : ℕ}
    (p : E ⟶ (Δ[n] : SSet.{u})) [RightFibration p]
    (a : (boundary n : SSet.{u}) ⟶ E) (ha : a ≫ p = (boundary n).ι) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ (boundary n : SSet.{u}) ⟶ E,
      prismEndpoint 1 (boundary n : SSet.{u}) ≫ H = a ∧
        H ≫ p = (Δ[1] ◁ (boundary n).ι) ≫ prismFirstContraction n := by
  have := rightAnodyneExtensions_point_whiskerRight (boundary n : SSet.{u}) p
    (RightFibration.mem (p := p))
  have sq : CommSq (snd (horn 1 1 : SSet.{u}) (boundary n : SSet.{u}) ≫ a)
      ((horn 1 1).ι ▷ (boundary n : SSet.{u})) p
      ((Δ[1] ◁ (boundary n).ι) ≫ prismFirstContraction n) := by
    constructor
    rw [Category.assoc, ha]
    rw [← Category.assoc ((horn 1 1).ι ▷ _), ← whisker_exchange,
      Category.assoc, prismFirstContraction_horn_one]
    rfl
  refine ⟨sq.lift, ?_, sq.fac_right⟩
  have h := congrArg (fun f ↦ hornOneLastSection (boundary n : SSet.{u}) ≫ f) sq.fac_left
  simpa only [← Category.assoc, hornOneLastSection_ι, hornOneLastSection_snd,
    Category.id_comp] using h

/-- 概要：境界ホモトピーの先頭は最初の頂点上の fiber へ写る。
方針：収縮の先頭が定値であることと端点の自然性を用いる。
規約：H は base の標準収縮を持ち上げる射。
使われ方：Kerodon Lemma 4.4.2.15 の fiber の可縮性の適用。 -/
lemma boundaryPrism_zero_comp {E : SSet.{u}} {n : ℕ}
    (p : E ⟶ (Δ[n] : SSet.{u}))
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary n : SSet.{u}) ⟶ E)
    (hH : H ≫ p = (Δ[1] ◁ (boundary n).ι) ≫ prismFirstContraction n) :
    (prismEndpoint 0 (boundary n : SSet.{u}) ≫ H) ≫ p =
      SSet.const (stdSimplex.obj₀Equiv.symm 0) := by
  rw [Category.assoc, hH, ← Category.assoc, prismEndpoint_naturality,
    Category.assoc, prismFirstContraction_zero, SSet.comp_const]

/-- 概要：最初の fiber が可縮なら境界ホモトピーの先頭を単体全体へ延長できる。
方針：定値性で fiber に持ち上げ、全境界の充填を使い元へ含める。
規約：延長の base も最初の頂点に定値。
使われ方：Kerodon Lemma 4.4.2.15 の prism の先頭の充填。 -/
lemma boundaryPrism_fillZero {E : SSet.{u}} {n : ℕ}
    (p : E ⟶ (Δ[n] : SSet.{u}))
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary n : SSet.{u}) ⟶ E)
    (hH : H ≫ p = (Δ[1] ◁ (boundary n).ι) ≫ prismFirstContraction n)
    (hc : IsContractibleKan (vertexFiber p (stdSimplex.obj₀Equiv.symm 0))) :
    ∃ F : (Δ[n] : SSet.{u}) ⟶ E,
      (boundary n).ι ≫ F = prismEndpoint 0 (boundary n : SSet.{u}) ≫ H ∧
        F ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm 0) := by
  let b := vertexFiberLift p (stdSimplex.obj₀Equiv.symm 0)
    (prismEndpoint 0 (boundary n : SSet.{u}) ≫ H) (boundaryPrism_zero_comp p H hH)
  obtain ⟨F, hF⟩ := hc n b
  refine ⟨F ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm 0), ?_, ?_⟩
  · rw [← Category.assoc, hF]
    exact vertexFiberLift_ι _ _ _ _
  · rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]

end SerrePositivity.InfinityCategories
