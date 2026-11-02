module
public import SerrePositivity.InfinityCategories.Core.IdentityCocone
public import SerrePositivity.InfinityCategories.F1.ColimitRestriction
public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleLongEdge
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness

/-! # 区間図式の終点余錐

概要：一本の辺の終点は、その区間図式の余極限である。
方針：終点を重複した二単体を余錐とし、right anodyne な終点包含への制限で判定する。
規約：終点側の余錐の辺は恒等射。使われ方：恒等辺を持つ押し出し四角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：区間の終点を重複する退化二単体で終点余錐を作る。
方針：標準 join の同型の後に最後の退化写像を合成する。
規約：値域の quasicategory 性は不要。使われ方：終点余錐の余極限性。 -/
def edgeTerminalCocone {X : SSet.{u}} (g : (Δ[1] : SSet.{u}) ⟶ X) : JoinCocone g :=
  ⟨(joinStdSimplexIso 1 0).hom ≫ stdSimplex.σ 1 ≫ g, by
    rw [← Category.assoc, joinStdSimplexIso_one_inl]
    have h : (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
        stdSimplex.σ 1 = 𝟙 Δ[1] := by
      apply stdSimplex_hom_ext_vertices
      apply ConcreteCategory.hom_ext
      intro q
      obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
      fin_cases i <;> rfl
    rw [← Category.assoc, h, Category.id_comp]⟩

/-- 概要：終点余錐を終点に制限すると恒等余錐となる。
方針：二つの標準区間への射を頂点で比較する。
規約：恒等余錐の定値写像として等号を述べる。使われ方：余極限性の反映。 -/
lemma edgeTerminalCocone_restrict_val {X : SSet.{u}} (g : (Δ[1] : SSet.{u}) ⟶ X) :
    ((edgeTerminalCocone g).restrict (stdSimplex.δ (0 : Fin 2))).val =
      SSet.const (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g)) := by
  have h : joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 (Δ[0] : SSet.{u})) ≫
      (joinStdSimplexIso 1 0).hom ≫ stdSimplex.σ 1 =
        SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    rw [← Category.assoc, joinStdSimplexIso_one_vertex]
    have hs : (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
        stdSimplex.σ 1 = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
      apply SSet.yonedaEquiv.injective
      decide
    change (joinStdSimplexIso 0 0).hom ≫ stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.σ 1 = _
    rw [hs, SSet.comp_const]
  change _ ≫ ((joinStdSimplexIso 1 0).hom ≫ stdSimplex.σ 1 ≫ g) = _
  rw [← Category.assoc, ← Category.assoc, Category.assoc _ _ (stdSimplex.σ 1), h, SSet.const_comp]
  have hv : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) =
      stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by decide
  rw [SSet.yonedaEquiv_comp, hv]

/-- 概要：区間図式の終点余錐は余極限である。
方針：right anodyne な終点包含に沿って恒等余錐へ制限する。
規約：値域は quasicategory。使われ方：退化押し出し四角形。 -/
lemma edgeTerminalCocone_isColimit {X : SSet.{u}} [Quasicategory X]
    (g : (Δ[1] : SSet.{u}) ⟶ X) : IsColimitCone (edgeTerminalCocone g) := by
  apply (isColimitCone_iff_restrict_of_rightAnodyne _ _ endpointInclusion_rightAnodyne).2
  exact isColimitCone_of_point_constant _ _ (edgeTerminalCocone_restrict_val g)

end SerrePositivity.InfinityCategories
