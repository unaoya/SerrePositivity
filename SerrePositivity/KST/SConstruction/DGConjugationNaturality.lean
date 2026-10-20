module
public import SerrePositivity.KST.SConstruction.DGClosedIsoConjugationLaws

/-! # 全 Hom 自然比較と共役の一致
概要：全 Hom 自然性の四角形から、共役後の Hom 作用の等号を得る。
方針：閉零同型の逆による前合成で比較を消去する。
規約：任意次数の Hom 射を比較する。使われ方：Perf 作用の恒等・合成法則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable (V : Type u) [Category V] [MonoidalCategory V]
  {C : Type v} [Category C] [EnrichedOrdinaryCategory V C]

/-- 元の全 Hom 自然性は、同じ比較同型による共役後の作用の等号を与える。 -/
lemma enrichedConjugation_of_naturality {K : V} {X X' Y Y' : C}
    (e : X ≅ X') (f : Y ≅ Y')
    (k : K ⟶ (X ⟶[V] Y)) (l : K ⟶ (X' ⟶[V] Y'))
    (h : k ≫ eHomWhiskerLeft V X f.hom = l ≫ eHomWhiskerRight V e.hom Y') :
    k ≫ enrichedClosedIsoConjugation V e f = l := by
  have hh := congrArg (fun a => a ≫ eHomWhiskerRight V e.inv Y') h
  simpa only [enrichedClosedIsoConjugation, Category.assoc,
    eHom_whisker_exchange, ← eHomWhiskerRight_comp_assoc,
    ← eHomWhiskerRight_comp, Iso.inv_hom_id,
    eHomWhiskerRight_id, Category.comp_id] using hh

end SerrePositivity.KST.SConstruction
