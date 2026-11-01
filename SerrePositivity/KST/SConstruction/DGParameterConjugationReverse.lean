module
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGConjugationNaturality

/-! # 元のパラメータ作用の比較共役の逆向き
概要：全 Hom の比較共役の等号を、同じ実同型の逆による共役へ移す。
方針：元の Hom 共役同型の逆律を使う。
規約：任意のパラメータを保つ。使われ方：実 tensor 結合比較の逆向き自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
variable (V : Type u) [Category V] [MonoidalCategory V]
  {C : Type v} [Category C] [EnrichedOrdinaryCategory V C]

/-- 元の全 Hom 共役の等号は、逆比較による元のパラメータ作用の回収を与える。 -/
lemma enrichedClosedIsoConjugation_reverse {K : V} {X X' Y Y' : C}
    (e : X ≅ X') (f : Y ≅ Y') (k : K ⟶ (X ⟶[V] Y)) (l : K ⟶ (X' ⟶[V] Y'))
    (h : k ≫ enrichedClosedIsoConjugation V e f = l) :
    l ≫ enrichedClosedIsoConjugation V e.symm f.symm = k := by
  rw [← h]
  change (k ≫ (enrichedClosedIsoHomIso V e f).hom) ≫
    (enrichedClosedIsoHomIso V e f).inv = k
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.KST.SConstruction
