module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomTwistedUnit

/-!
概要：実際の零次 twisted arrow を読み戻して比較射で戻すと、元の指定単体に戻る。
方針：既存の長い一次射列の外延性を使い、中央の射を恒等・合成の法則で比較する。
規約：全次数の余単位とは分け、零次の指定射の計算を固定する。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）、HTT 5.1.5.6 の模型比較の余単位則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable {C : Type u} [SmallCategory C]

/-- 元の零次 twisted arrow の単体は読み戻しと指定比較の往復で変わらない。
Kerodon Proposition 8.1.1.10（Tag 03JN）、零次の余単位則。 -/
lemma ordinaryHomTwistedSimplex_read_point (f : (TwistedArrow (nerve C)) _⦋0⦌) :
    ordinaryHomTwistedSimplex (ordinaryHomTwistedRead f) = f := by
  let L := edgewiseSimplexEquiv (nerve C) 0 f
  apply (edgewiseSimplexEquiv (nerve C) 0).injective
  refine ComposableArrows.ext₁ (by rfl) (by rfl) ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change L.map (𝟙 (0 : Fin 2)) ≫ L.map (homOfLE (show (0 : Fin 2) ≤ 1 by decide)) ≫
    L.map (𝟙 (1 : Fin 2)) = L.map (homOfLE (show (0 : Fin 2) ≤ 1 by decide))
  rw [L.map_id, L.map_id]
  simp only [Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
