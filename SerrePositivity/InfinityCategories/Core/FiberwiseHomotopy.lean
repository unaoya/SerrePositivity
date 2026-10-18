module

public import SerrePositivity.InfinityCategories.Core.FiberEdgeCorrection

/-!
概要：同値である Fibration の逆合成を fiber 内で恒等射へ移す。
方針：厳密な切断を選び、内部 Hom の辺を退化三角形で補正する。
規約：標的への射影が恒等辺となる実際の辺を構成する。
使われ方：HTT §2.2、Kerodon §4.8.4 の可縮な fiber の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
  HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：同値である Fibration は切断と、射影が恒等辺である逆合成から恒等関手への辺を持つ。
方針：厳密な切断を選び、単位の辺を内部 Hom の fiber 内の辺へ補正する。
規約：相対的な辺の存在を具体的なデータとして主張する。
使われ方：HTT §2.2、Kerodon §4.8.4 の全境界の持ち上げへの移行。 -/
lemma fibration_exists_section_and_relativeFunctorEdge {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [Fibration p]
    (he : IsQCatEquivalence p) :
    ∃ s : B ⟶ E, s ≫ p = 𝟙 B ∧
      ∃ k : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom E).obj E))
        (functorVertex (p ≫ s)) (functorVertex (𝟙 E)),
        ((ihom E).map p).app (Opposite.op ⦋1⦌) k.edge =
          (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom E).obj B))
            (functorVertex p)).edge := by
  obtain ⟨s, hs⟩ := fibration_exists_section_of_isQCatEquivalence p he
  obtain ⟨e⟩ := he.functorIsoOfSection s hs
  let q := (ihom E).map p
  let t := (ihom E).map s
  have ht : t ≫ q = 𝟙 ((ihom E).obj B) := by
    rw [← CategoryTheory.Functor.map_comp, hs, CategoryTheory.Functor.map_id]
  have hx : t.app (Opposite.op ⦋0⦌) (q.app (Opposite.op ⦋0⦌)
      (functorVertex (p ≫ s))) = functorVertex (p ≫ s) := by
    change functorVertex (((p ≫ s) ≫ p) ≫ s) = _
    rw [Category.assoc p s p, hs, Category.comp_id]
  have hy : t.app (Opposite.op ⦋0⦌) (q.app (Opposite.op ⦋0⦌)
      (functorVertex (𝟙 E))) = functorVertex (p ≫ s) := by
    change functorVertex (((𝟙 E) ≫ p) ≫ s) = _
    rw [Category.id_comp]
  have hxy : q.app (Opposite.op ⦋0⦌) (functorVertex (p ≫ s)) =
      q.app (Opposite.op ⦋0⦌) (functorVertex (𝟙 E)) := by
    change functorVertex ((p ≫ s) ≫ p) = functorVertex ((𝟙 E) ≫ p)
    rw [Category.assoc, hs, Category.comp_id, Category.id_comp]
  obtain ⟨k, hk⟩ := leftFibration_correct_edge_over_identity q t ht (FunctorIso.edge e) hx hy hxy
  refine ⟨s, hs, k, ?_⟩
  exact hk

/-- 概要：関手の辺の射影が恒等辺なら、対応するホモトピーの射影は時刻に定値。
方針：uncurry の後合成の自然性と Yoneda 表示を計算する。
規約：標準的なホモトピーの区間は第二因子。
使われ方：HTT §2.2 の fiber 内の実際のホモトピー。 -/
lemma simplicialHomotopyOfFunctorEdge_comp_eq_constant {A E B : SSet.{u}}
    {f g : A ⟶ E} (p : E ⟶ B) (b : A ⟶ B)
    (k : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj E))
      (functorVertex f) (functorVertex g))
    (hk : ((ihom A).map p).app (Opposite.op ⦋1⦌) k.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj B))
        (functorVertex b)).edge) :
    (simplicialHomotopyOfFunctorEdge k).h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ b := by
  change uncurry (SSet.yonedaEquiv.symm k.edge) ≫ p = _
  rw [← uncurry_natural_right, SSet.yonedaEquiv_symm_comp]
  change uncurry (SSet.yonedaEquiv.symm
    (((ihom A).map p).app (Opposite.op ⦋1⦌) k.edge)) = _
  rw [hk]
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  dsimp [SSet.Truncated.Edge.id, functorVertex, uncurry]
  rfl

end SerrePositivity.InfinityCategories
