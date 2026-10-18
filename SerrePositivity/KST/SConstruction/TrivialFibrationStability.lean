module
public import SerrePositivity.KST.SConstruction.TrivialFibrationUniversality

/-! # trivial Kan fibration に沿う安定性の反映
概要：安定な quasicategory を標的に持つ trivial Kan fibration の源は安定。
方針：零対象を切断で持ち上げ、fiber/cofiber 正方形を指定された辺を保って持ち上げる。
規約：α-S の IsStable をそのまま使い、Core の公開名・型を変更しない。
使われ方：S_n と第一行の図式圏の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：安定性の反映で使う右辺の包含は単射。
方針：第二成分が恒等の積への持ち上げであることを使う。
規約：正方形の右辺。使われ方：fiber 正方形の相対持ち上げ。 -/
lemma squareRightEdge_mono : Mono (squareRightEdge.{u}) := by
  change Mono (lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})))
  infer_instance

/-- 概要：安定性の反映で使う下辺の包含は単射。
方針：第一成分が恒等の積への持ち上げであることを使う。
規約：正方形の下辺。使われ方：cofiber 正方形の相対持ち上げ。 -/
lemma squareBottomEdge_mono : Mono (squareBottomEdge.{u}) := by
  change Mono (lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
  infer_instance

/-- 概要：零対象の存在は trivial Kan fibration で源へ反映する。
方針：切断で標的の零頂点を持ち上げ、零対象性の反映を使う。
規約：両端は quasicategory。使われ方：安定性の零対象条件。 -/
lemma hasZeroVertex_of_trivialKanFibration {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    [HasZeroVertex B] (q : E ⟶ B) [TrivialKanFibration q] : HasZeroVertex E := by
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section q
  let z := (chosenZeroVertex B).vertex
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app hs (Opposite.op ⦋0⦌)) z
  have hz : IsZeroVertex (q.app (Opposite.op ⦋0⦌) (s.app (Opposite.op ⦋0⦌) z)) :=
    he.symm ▸ (chosenZeroVertex B).isZero
  exact ⟨⟨_, (isZeroVertex_iff_of_trivialKanFibration q _).2 hz⟩⟩

/-- 概要：指定された辺の fiber 正方形を trivial Kan fibration に沿って持ち上げる。
方針：右辺包含の単射に対する RLP と、零角・引き戻し性の反映を使う。
規約：源で与えた辺を厳密に保つ。使われ方：安定性の fiber の存在。 -/
lemma fiberSquare_nonempty_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] [IsStable B] (q : E ⟶ B) [TrivialKanFibration q]
    {x y : E _⦋0⦌} (f : SSet.Truncated.Edge (X := (truncation 2).obj E) x y) :
    Nonempty (FiberSquare f) := by
  let t := chosenFiberSquare (f.map ((truncation 2).map q))
  have he : squareRightEdge ≫ t.square = SSet.yonedaEquiv.symm f.edge ≫ q :=
    t.right_edge.trans (SSet.yonedaEquiv_symm_comp f.edge q).symm
  have := TrivialKanFibration.mem (p := q) squareRightEdge squareRightEdge_mono
  have h : CommSq (SSet.yonedaEquiv.symm f.edge) squareRightEdge q t.square := ⟨he.symm⟩
  exact ⟨{
    square := h.lift
    zero_corner := by
      apply (isZeroVertex_iff_of_trivialKanFibration q _).2
      change IsZeroVertex (squareVertex (h.lift ≫ q) 0 1)
      rw [h.fac_right]
      exact t.zero_corner
    right_edge := h.fac_left
    isPullback := by
      apply (isPullbackSquare_iff_postcomp_of_trivialKanFibration q _).2
      rw [h.fac_right]
      exact t.isPullback }⟩

/-- 概要：指定された辺の cofiber 正方形を trivial Kan fibration に沿って持ち上げる。
方針：下辺包含の単射に対する RLP と、零角・押し出し性の反映を使う。
規約：源で与えた辺を厳密に保つ。使われ方：安定性の cofiber の存在。 -/
lemma cofiberSquare_nonempty_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] [IsStable B] (q : E ⟶ B) [TrivialKanFibration q]
    {x y : E _⦋0⦌} (f : SSet.Truncated.Edge (X := (truncation 2).obj E) x y) :
    Nonempty (CofiberSquare f) := by
  let t := chosenCofiberSquare (f.map ((truncation 2).map q))
  have he : squareBottomEdge ≫ t.square = SSet.yonedaEquiv.symm f.edge ≫ q :=
    t.bottom_edge.trans (SSet.yonedaEquiv_symm_comp f.edge q).symm
  have := TrivialKanFibration.mem (p := q) squareBottomEdge squareBottomEdge_mono
  have h : CommSq (SSet.yonedaEquiv.symm f.edge) squareBottomEdge q t.square := ⟨he.symm⟩
  exact ⟨{
    square := h.lift
    zero_corner := by
      apply (isZeroVertex_iff_of_trivialKanFibration q _).2
      change IsZeroVertex (squareVertex (h.lift ≫ q) 0 1)
      rw [h.fac_right]
      exact t.zero_corner
    bottom_edge := h.fac_left
    isPushout := by
      apply (isPushoutSquare_iff_postcomp_of_trivialKanFibration q _).2
      rw [h.fac_right]
      exact t.isPushout }⟩

/-- 概要：trivial Kan fibration の標的が安定なら源も安定。
方針：零対象と fiber/cofiber の存在を持ち上げ、零角の双方向の普遍性を反映する。
規約：追加の源の安定性仮定を置かない。使われ方：第一行との比較による S_n の安定性。 -/
lemma isStable_of_trivialKanFibration {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    [IsStable B] (q : E ⟶ B) [TrivialKanFibration q] : IsStable E where
  toHasZeroVertex := hasZeroVertex_of_trivialKanFibration q
  fiber_exists f := fiberSquare_nonempty_of_trivialKanFibration q f
  cofiber_exists f := cofiberSquare_nonempty_of_trivialKanFibration q f
  fiber_iff_cofiber t := by
    let b : ZeroTriangle B := ⟨t.square ≫ q,
      (isZeroVertex_iff_of_trivialKanFibration q _).1 t.zero_corner⟩
    exact (isPullbackSquare_iff_postcomp_of_trivialKanFibration q t.square).trans
      ((IsStable.fiber_iff_cofiber b).trans
        (isPushoutSquare_iff_postcomp_of_trivialKanFibration q t.square).symm)

end SerrePositivity.KST.SConstruction
