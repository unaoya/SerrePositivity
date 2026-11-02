module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorClosedNaturality

/-! # 全 Hom 自然な閉比較の合成
概要：元の閉比較を合成した同じ射族の全 Hom 自然性を証明する。
方針：前後合成の交換を使い、元の二つの可換正方形を貼る。
規約：元の比較射を変更しない。使われ方：実 Perf 四角形の三つの比較の合成。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable (V : Type u) [Category V] [MonoidalCategory V]
  {C : Type v} [Category C] [EnrichedOrdinaryCategory V C]

/-- 同じ二つの全 Hom 自然な閉比較の合成も、全 Hom 上で自然。 -/
lemma dgClosedComparison_comp {K : V} {X X' Y Y' Z Z' : C}
    (a : X ⟶ Y) (a' : X' ⟶ Y') (b : Y ⟶ Z) (b' : Y' ⟶ Z')
    (k : K ⟶ (X ⟶[V] X')) (l : K ⟶ (Y ⟶[V] Y')) (m : K ⟶ (Z ⟶[V] Z'))
    (ha : k ≫ eHomWhiskerLeft V X a' = l ≫ eHomWhiskerRight V a Y')
    (hb : l ≫ eHomWhiskerLeft V Y b' = m ≫ eHomWhiskerRight V b Z') :
    k ≫ eHomWhiskerLeft V X (a' ≫ b') =
      m ≫ eHomWhiskerRight V (a ≫ b) Z' := by
  rw [eHomWhiskerLeft_comp, ← Category.assoc, ha, Category.assoc,
    ← eHom_whisker_exchange, ← Category.assoc, hb, Category.assoc,
    ← eHomWhiskerRight_comp]

end SerrePositivity.KST.SConstruction
