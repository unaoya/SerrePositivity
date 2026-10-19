module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTransportTriangle
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeTrianglePrismHomotopy
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-!
概要：同じ native な二単体と標準二辺を持つ輸送三角形の選択を、境界を固定して比較する。
方針：内ホーン上で定値な相対円柱を選び、同じ円柱を長辺へ制限する。
規約：円柱の底・二辺・長辺の端点条件を一緒に保持する。
使われ方：輸送三角形の選択を替えても、全 Hom の境界比較を整合させるための入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  {a b c : B _⦋0⦌} {e : B.Edge a b} {f : B.Edge b c} {g : B.Edge a c}
  (σ : SSet.Edge.CompStruct e f g)
  (T T' : CoherentTransportTriangle p σ)

/-- 三角形全体の比較と、底・標準二辺を固定する円柱の式。 -/
structure CoherentTransportTriangleHomotopy where
  homotopy : SSet.Homotopy T.prism T'.prism
  projection : homotopy.h ≫ p =
    fst ((Δ[2] : SSet.{u}) ⊗ vertexFiber p a) Δ[1] ≫
      fst (Δ[2] : SSet.{u}) (vertexFiber p a) ≫ SSet.yonedaEquiv.symm σ.simplex
  first : ((stdSimplex.δ (2 : Fin 3) ▷ vertexFiber p a) ▷ (Δ[1] : SSet.{u})) ≫
    homotopy.h = fst ((Δ[1] : SSet.{u}) ⊗ vertexFiber p a) Δ[1] ≫ transportEdgePrism p e
  second : ((stdSimplex.δ (0 : Fin 3) ▷ vertexFiber p a) ▷ (Δ[1] : SSet.{u})) ≫
    homotopy.h = fst ((Δ[1] : SSet.{u}) ⊗ vertexFiber p a) Δ[1] ≫
      (Δ[1] ◁ edgeTransport p e) ≫ transportEdgePrism p f

/-- 同じ底と標準二辺を持つ実際の輸送三角形を、二辺を保つ円柱で比較する。 -/
def coherentTransportTriangleHomotopy : CoherentTransportTriangleHomotopy p σ T T' :=
  Classical.choice (by
    obtain ⟨H, hbase, hfirst, hsecond⟩ := exists_trianglePrism_homotopy_relative_spine p
      (fst (Δ[2] : SSet.{u}) (vertexFiber p a) ≫ SSet.yonedaEquiv.symm σ.simplex)
      T.prism T'.prism T.projection T'.projection
      (T.first.trans T'.first.symm) (T.second.trans T'.second.symm)
    exact ⟨⟨H, by simpa only [Category.assoc] using hbase,
      by simpa only [← Category.assoc, T'.first] using hfirst,
      by simpa only [← Category.assoc, T'.second, Category.assoc] using hsecond⟩⟩)

/-- 同じ比較円柱を長辺へ制限する。 -/
def coherentTransportTriangleLongHomotopy :
    SSet.Homotopy ((stdSimplex.δ (1 : Fin 3) ▷ vertexFiber p a) ≫ T.prism)
      ((stdSimplex.δ (1 : Fin 3) ▷ vertexFiber p a) ≫ T'.prism) :=
  functorHomotopyPrecomp (coherentTransportTriangleHomotopy p σ T T').homotopy
    (stdSimplex.δ (1 : Fin 3) ▷ vertexFiber p a)

/-- 長辺の円柱の底は、元の長辺上で時間方向に定値。 -/
lemma coherentTransportTriangleLongHomotopy_projection :
    (coherentTransportTriangleLongHomotopy p σ T T').h ≫ p =
      fst ((Δ[1] : SSet.{u}) ⊗ vertexFiber p a) Δ[1] ≫
        fst (Δ[1] : SSet.{u}) (vertexFiber p a) ≫ SSet.yonedaEquiv.symm g.edge := by
  dsimp only [coherentTransportTriangleLongHomotopy, functorHomotopyPrecomp]
  rw [Category.assoc, (coherentTransportTriangleHomotopy p σ T T').projection,
    ← Category.assoc, whiskerRight_fst, Category.assoc]
  change _ ≫ (fst (Δ[1] : SSet.{u}) (vertexFiber p a) ≫
    stdSimplex.δ (1 : Fin 3)) ≫ SSet.yonedaEquiv.symm σ.simplex = _
  rw [Category.assoc, σ.δ_one_yonedaEquiv_symm]

/-- 長辺の始点は、元の始点 fiber の包含上で時間方向に定値。 -/
lemma coherentTransportTriangleLongHomotopy_zero :
    (prismEndpoint 0 (vertexFiber p a) ▷ (Δ[1] : SSet.{u})) ≫
        (coherentTransportTriangleLongHomotopy p σ T T').h =
      fst (vertexFiber p a) Δ[1] ≫ vertexFiberι p a := by
  let A := vertexFiber p a
  have hz : prismEndpoint 0 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) =
      prismEndpoint 0 A ≫ (stdSimplex.δ (2 : Fin 3) ▷ A) := rfl
  dsimp only [coherentTransportTriangleLongHomotopy, functorHomotopyPrecomp]
  rw [← Category.assoc, ← comp_whiskerRight, hz, comp_whiskerRight, Category.assoc,
    (coherentTransportTriangleHomotopy p σ T T').first, ← Category.assoc,
    whiskerRight_fst, Category.assoc, transportEdgePrism_zero]

/-- 長辺の終点は、二段階輸送の同じ関手上で時間方向に定値。 -/
lemma coherentTransportTriangleLongHomotopy_one :
    (prismEndpoint 1 (vertexFiber p a) ▷ (Δ[1] : SSet.{u})) ≫
        (coherentTransportTriangleLongHomotopy p σ T T').h =
      fst (vertexFiber p a) Δ[1] ≫
        (edgeTransport p e ≫ edgeTransport p f) ≫ vertexFiberι p c := by
  let A := vertexFiber p a
  have ho : prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) =
      prismEndpoint 1 A ≫ (stdSimplex.δ (0 : Fin 3) ▷ A) := rfl
  dsimp only [coherentTransportTriangleLongHomotopy, functorHomotopyPrecomp]
  rw [← Category.assoc, ← comp_whiskerRight, ho, comp_whiskerRight, Category.assoc,
    (coherentTransportTriangleHomotopy p σ T T').second, ← Category.assoc,
    whiskerRight_fst, Category.assoc, ← Category.assoc (prismEndpoint 1 A),
    prismEndpoint_naturality, Category.assoc, transportEdgePrism_one, Category.assoc]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
