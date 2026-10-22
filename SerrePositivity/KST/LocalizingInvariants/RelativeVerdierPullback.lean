module

public import SerrePositivity.KST.LocalizingInvariants.RelativeInvariant
public import SerrePositivity.InfinityCategories.Stable.PullbackPasting
public import SerrePositivity.InfinityCategories.Stable.SquareTranspose

/-!
概要：提示源内の Verdier 比較長方形から、同じ値関手の実 pullback を導く。
方針：右面・外周の転置 Verdier 提示を E で写し、実 pullback 貼合せで右面を消す。
規約：長方形と全合成三角形を S 内で保持する。使われ方：相対版 K-8 d8。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- D2・β3 の S 内の持ち上げが供給する、右面と外周の Verdier 比較。 -/
structure RelativeVerdierRectangle {S : SSet.{u + 1}} (ν : S ⟶ StableInfinity.{u}) where
  diagram : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S
  right : RelativeVerdierDiagram ν
  outer : RelativeVerdierDiagram ν
  right_eq : pastingSquare diagram 0 = (β_ _ _).hom ≫ right.square
  outer_eq : pastingSquare diagram 1 = (β_ _ _).hom ≫ outer.square

namespace RelativeVerdierRectangle
variable {S : SSet.{u + 1}} {ν : S ⟶ StableInfinity.{u}}
  (d : RelativeVerdierRectangle ν)

/-- ν 像の二つの Verdier 提示から、S 内の実長方形の相対証明書を作る。 -/
def ofImage (F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S)
    (r o : VerdierDiagram.{u})
    (hR : pastingSquare (F ≫ ν) 0 = (β_ _ _).hom ≫ r.square)
    (hO : pastingSquare (F ≫ ν) 1 = (β_ _ _).hom ≫ o.square) :
    RelativeVerdierRectangle ν where
  diagram := F
  right := ⟨(β_ _ _).hom ≫ pastingSquare F 0, r, by
    rw [Category.assoc]
    change (β_ _ _).hom ≫ pastingSquare (F ≫ ν) 0 = r.square
    rw [hR, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]⟩
  outer := ⟨(β_ _ _).hom ≫ pastingSquare F 1, o, by
    rw [Category.assoc]
    change (β_ _ _).hom ≫ pastingSquare (F ≫ ν) 1 = o.square
    rw [hO, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]⟩
  right_eq := by
    change _ = (β_ _ _).hom ≫ (β_ _ _).hom ≫ _
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  outer_eq := by
    change _ = (β_ _ _).hom ≫ (β_ _ _).hom ≫ _
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- 元の二脚と比較三角形を含む S 内の比較正方形。 -/
def comparisonSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S :=
  (β_ _ _).hom ≫ pastingSquare d.diagram 2

/-- fiber 列二つから得る d8 の比較 pullback。E の絶対版への延長は不要。 -/
lemma comparisonSquare_isPullback {E : S ⟶ Spectra.Sp.{u}}
    (hE : IsRelativeLocalizingInvariant ν E) :
    IsPullbackSquare (d.comparisonSquare ≫ E) := by
  have hR : IsPullbackSquare (pastingSquare (d.diagram ≫ E) 0) := by
    change IsPullbackSquare (pastingSquare d.diagram 0 ≫ E)
    rw [d.right_eq]
    exact (isPullbackSquare_iff_transpose (d.right.square ≫ E)).mp
      (hE.preservesVerdier d.right)
  have hO : IsPullbackSquare (pastingSquare (d.diagram ≫ E) 1) := by
    change IsPullbackSquare (pastingSquare d.diagram 1 ≫ E)
    rw [d.outer_eq]
    exact (isPullbackSquare_iff_transpose (d.outer.square ≫ E)).mp
      (hE.preservesVerdier d.outer)
  exact (isPullbackSquare_iff_transpose (pastingSquare d.diagram 2 ≫ E)).mp
    (isPullbackSquare_pasting_cancel_right (d.diagram ≫ E) hR hO)

/-- 元の E 値の同じ cospan 上の実極限錐。 -/
def comparisonCone (E : S ⟶ Spectra.Sp.{u}) := pullbackCone (d.comparisonSquare ≫ E)

lemma comparisonCone_isLimit {E : S ⟶ Spectra.Sp.{u}}
    (hE : IsRelativeLocalizingInvariant ν E) : IsLimitCone (d.comparisonCone E) :=
  d.comparisonSquare_isPullback hE

end RelativeVerdierRectangle
end SerrePositivity.KST.LocalizingInvariants
