module
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingReindex
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.Projection

/-!
概要：同じ反変・共変の両端を持つ全射の要素を、一つのtwisted arrowの全写像へ送る。
方針：元の長い単体を同じedgewise重みの同型で戻し、全再添字付けの等式を使う。
規約：IS-W2 R03dの同じ射列の全自然性。点ごとの写像の選択ではない。
使われ方：元の全source frameの要素圏から正本Hom∞への表示された比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open CategoryTheory SSet
open scoped Simplicial

/-- 同じ標準単体表示は、実際のedgewise重みの全射と両立する。 -/
theorem twistedPairingWeightIso_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    edgewiseWeight.{u}.map α ≫ (edgewiseWeightIso n).hom =
      (edgewiseWeightIso m).hom ≫ stdSimplex.map
        (SimplexCategory.mkHom (edgewiseWeightReindexOrderHom.{u} α)) := by
  rw [edgewiseWeightReindexOrderHom_map, edgewiseWeightStandardMap, Iso.hom_inv_id_assoc]

variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
  (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j)

/-- 元の両端と元の射の全列を、一つのtwisted arrowの全単体写像として束ねる。 -/
def twistedPairingNerveMap : nerve I ⟶ TwistedArrow (nerve C) where
  app n := ↾fun σ => (edgewiseWeightIso n.unop.len).hom ≫
    (SSet.yonedaEquiv (X := nerve C)).symm (twistedPairingSimplex A B h σ)
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro σ
    change Fin (n.unop.len+1) ⥤ I at σ
    change (edgewiseWeightIso m.unop.len).hom ≫
      (SSet.yonedaEquiv (X := nerve C)).symm (twistedPairingSimplex A B h (f.unop.toOrderHom.monotone.functor ⋙ σ)) =
      edgewiseWeight.map f.unop ≫ ((edgewiseWeightIso n.unop.len).hom ≫
        (SSet.yonedaEquiv (X := nerve C)).symm (twistedPairingSimplex A B h σ))
    rw [← Category.assoc, twistedPairingWeightIso_reindex, Category.assoc,
      SSet.yonedaEquiv_symm_naturality_left]
    exact congrArg (fun τ : ComposableArrows C (m.unop.len+m.unop.len+1) =>
      (edgewiseWeightIso m.unop.len).hom ≫ (SSet.yonedaEquiv (X := nerve C)).symm τ)
        (twistedPairingSimplex_reindex f.unop A B h hh σ).symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
