module
public import SerrePositivity.InfinityCategories.Derived.DGUnitCompositionEvaluation
/-!
概要：単位からの実射と全 Hom の自然性を、同じ厳密 dg 比較へ接続する。
方針：元の斉次合成と実分解の三成分の等式を使う。
規約：出力の射影性と入力の Small 性は不要。使われ方：模型変更の全自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R] {E : Type v} [DGCategory R E]
variable {C : Type w} [DGCategory R C] {F G : DGFunctor R C E}
def dgStrictNatTransOfUnitNaturality
    (i : ∀ x, 𝟙_ (Complex R) ⟶ homObject R E (F.obj x) (G.obj x))
    (hi : ∀ x y, F.map x y ≫
      (ρ_ (homObject R E (F.obj x) (F.obj y))).inv ≫
        _ ◁ i y ≫ eComp (Complex R) (F.obj x) (F.obj y) (G.obj y) =
      G.map x y ≫ (λ_ (homObject R E (G.obj x) (G.obj y))).inv ≫
        i x ▷ _ ≫ eComp (Complex R) (F.obj x) (G.obj x) (G.obj y)) :
    StrictNatTrans F G where
  app x := cycleFromUnit _ (i x)
  naturality {x y k} f := by
    have he := congrArg (fun h => h.f k f) (hi x y)
    change (((ρ_ _).inv ≫ _ ◁ i y ≫
      eComp (Complex R) (F.obj x) (F.obj y) (G.obj y)).f k) ((F.map x y).f k f) =
      (((λ_ _).inv ≫ i x ▷ _ ≫
        eComp (Complex R) (F.obj x) (G.obj x) (G.obj y)).f k) ((G.map x y).f k f) at he
    rw [dgUnitPostcomp_apply, dgUnitPrecomp_apply] at he
    exact he
def dgStrictNatTransOfUnitMapNaturality
    (i : ∀ x, 𝟙_ (Complex R) ⟶ homObject R E (F.obj x) (G.obj x))
    (hi : ∀ x y, F.map x y ≫ dgUnitPostcompMap (R := R) (D := E)
      (x := F.obj x) (y := F.obj y) (z := G.obj y) (i y) =
      G.map x y ≫ dgUnitPrecompMap (R := R) (D := E)
        (x := F.obj x) (y := G.obj x) (z := G.obj y) (i x)) :
    StrictNatTrans F G :=
  dgStrictNatTransOfUnitNaturality i (by
    intro x y
    simpa only [dgUnitPostcompMap, dgUnitPrecompMap, Category.assoc] using hi x y)
end SerrePositivity.InfinityCategories
