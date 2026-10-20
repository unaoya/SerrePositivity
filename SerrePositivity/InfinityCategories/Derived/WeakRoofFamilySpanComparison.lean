module
public import SerrePositivity.InfinityCategories.Derived.WeakHomotopyDescent
public import SerrePositivity.InfinityCategories.Stable.SpanHomotopyGluing
/-!
概要：弱同値で含まれる Kan fiber の二族を、実屋根内の輸送と比較から照合する。
方針：Kan 値の一つのホモトピー逆評価に全比較を送り、同じ内部 Hom の成分を照合する。
規約：全パラメータ族を一度に比較する。使われ方：商内の指定評価族と元の商 Hom 族の比較。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
/-- Kan fiber の二つの族は、実全空間内の共通の輸送付き比較からホモトピックになる。 -/
lemma weakRoofFamilySpanComparison {K Z E : SSet.{u}} [KanComplex Z]
    (j : Z ⟶ E) (hj : IsWeakHomotopyEquivalence j)
    (a₀ a : K ⟶ E) (b c : K ⟶ Z) (T : SSet.Homotopy a₀ a)
    (Hb : SSet.Homotopy a (b ≫ j)) (Hc : SSet.Homotopy a₀ (c ≫ j)) :
    Nonempty (SSet.Homotopy c b) := by
  obtain ⟨r, ⟨R⟩⟩ := hj.homotopyExtension (𝟙 Z)
  have hb := (functorVertex_piZero_eq_iff_homotopy _ _).mpr
    ⟨stableHomotopyRetarget (functorHomotopyPrecomp R b)
      (Category.assoc b j r).symm (Category.comp_id b)⟩
  have hc := (functorVertex_piZero_eq_iff_homotopy _ _).mpr
    ⟨stableHomotopyRetarget (functorHomotopyPrecomp R c)
      (Category.assoc c j r).symm (Category.comp_id c)⟩
  have ht := (functorVertex_piZero_eq_iff_homotopy _ _).mpr
    ⟨functorHomotopyPostcomp T r⟩
  have hB := (functorVertex_piZero_eq_iff_homotopy _ _).mpr
    ⟨functorHomotopyPostcomp Hb r⟩
  have hC := (functorVertex_piZero_eq_iff_homotopy _ _).mpr
    ⟨functorHomotopyPostcomp Hc r⟩
  exact (functorVertex_piZero_eq_iff_homotopy _ _).mp
    (hc.symm.trans (hC.symm.trans (ht.trans (hB.trans hb))))
end SerrePositivity.InfinityCategories
