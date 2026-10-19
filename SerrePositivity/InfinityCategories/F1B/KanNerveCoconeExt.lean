module

public import SerrePositivity.InfinityCategories.F1B.KanNerveCoconeLeg
public import SerrePositivity.InfinityCategories.F1B.KanNerveCoconeVertex
public import SerrePositivity.InfinityCategories.F1B.KanNerveExtOne

/-!
概要：通常の余錐と native な余錐の比較の自然性を構成する。
方針：join の両境界と脚の一次単体を照合する。
規約：元の図式・頂点・指定脚を保つ厳密な等式。
使われ方：B5 の左 Kan の標準余錐と指定輸送の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B


/-- 概要：nerve と点の join からの射は両境界と全ての脚で決まる。
方針：余錐の境界と全ての脚を比較する。
規約：同じ宇宙の小さい圏の指定図式を扱う。
使われ方：B5 の指定局所余錐の古典比較。 -/
lemma kanNerve_joinTerminal_hom_ext {I C : Type u} [Category.{u} I] [Category.{u} C]
    {f g : join (nerve I) (Δ[0] : SSet.{u}) ⟶ nerve C}
    (h₀ : joinInl (nerve I) (Δ[0] : SSet.{u}) ≫ f = joinInl _ _ ≫ g)
    (h₁ : joinInr (nerve I) (Δ[0] : SSet.{u}) ≫ f = joinInr _ _ ≫ g)
    (he : ∀ i : I, f.app (Opposite.op ⦋1⦌) (kanJoinCoconeLegSimplex (nerveVertex i)) =
      g.app _ (kanJoinCoconeLegSimplex (nerveVertex i))) : f = g := by
  apply kanNerve_hom_ext_one
  rintro ⟨l, a, b⟩
  fin_cases l
  · cases a
    exact ConcreteCategory.congr_hom (NatTrans.congr_app h₁ (Opposite.op ⦋1⦌)) b
  · change (nerve I) _⦋0⦌ at a
    change (Δ[0] : SSet.{u}) _⦋0⦌ at b
    have hb : b = stdSimplex.objEquiv.symm (𝟙 ⦋0⦌) := by
      apply stdSimplex.ext
      intro i
      apply Fin.ext
      omega
    subst b
    obtain ⟨i, rfl⟩ := (nerveEquiv (C := I)).symm.surjective a
    exact he i
  · cases b
    exact ConcreteCategory.congr_hom (NatTrans.congr_app h₀ (Opposite.op ⦋1⦌)) a

/-- 概要：余錐の点側の制限は元の指定頂点の包含に一致する。
方針：余錐の境界と全ての脚を比較する。
規約：同じ宇宙の小さい圏の指定図式を扱う。
使われ方：B5 の指定局所余錐の古典比較。 -/
lemma kanNerveCocone_point {I C : Type u} [Category.{u} I] [Category.{u} C]
    {F : I ⥤ C} (c : Cocone F) :
    joinInr (nerve I) (Δ[0] : SSet.{u}) ≫ (kanNerveCoconeEquiv c).val = nervePoint c.pt := by
  apply SSet.yonedaEquiv.injective
  change (kanNerveCoconeEquiv c).vertex = nerveVertex c.pt
  exact kanNerveCocone_vertex c

/-- 概要：余錐の混合辺は添字への射と可換。
方針：余錐の境界と全ての脚を比較する。
規約：同じ宇宙の小さい圏の指定図式を扱う。
使われ方：B5 の指定局所余錐の古典比較。 -/
lemma kanJoinCoconeLegSimplex_natural {K L : SSet.{u}} (f : K ⟶ L) (x : K _⦋0⦌) :
    (joinMap f (𝟙 (Δ[0] : SSet.{u}))).app (Opposite.op ⦋1⦌)
      (kanJoinCoconeLegSimplex x) = kanJoinCoconeLegSimplex (f.app (Opposite.op ⦋0⦌) x) := rfl

end SerrePositivity.InfinityCategories.F1B
