module
public import SerrePositivity.KST.SConstruction.DGHomGluingActions
public import SerrePositivity.KST.SConstruction.DGStrictGluingFunctor
public import SerrePositivity.KST.SConstruction.DGClosedComparisonElements
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ActionYoneda

/-! # Hom 双加群内の閉比較族の全次数自然性
概要：元の標的内の閉比較を、同じ Hom gluing 双加群の自然な閉元へ移す。
方針：元の全 Hom 自然性を左右作用へ照合し、Yoneda 同型で実 augmentation へ戻す。
規約：標的の Small 性を要求しない。使われ方：Milnor 四角形の標準対角。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
private lemma prependThreeEq {V : Type*} [Category V]
    {A B C D E : V} (f : A ⟶ B) (g : B ⟶ C) (j : C ⟶ D) (k : D ⟶ E)
    (r : B ⟶ E) (h : g ≫ j ≫ k = r) : ((f ≫ g) ≫ j) ≫ k = f ≫ r := by
  simpa only [Category.assoc] using congrArg (fun z => f ≫ z) h

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  {P : Type t} [DGCategory R P] (L : DGFunctor R P C) (G : DGFunctor R P D)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (p.obj (L.obj x)) ⟶
    ForgetEnrichment.of (Complex R) (q.obj (G.obj x)))
  (h : ∀ x y, (L.comp p).map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (p.obj (L.obj x))) (a y) =
    (G.comp q).map x y ≫ eHomWhiskerRight (Complex R) (a x)
      (ForgetEnrichment.of (Complex R) (q.obj (G.obj y))))

/-- 元の閉比較を同じ Hom 双加群内の閉元として読む。 -/
def dgHomGluingComparisonCycle (x : P) :
    zeroCycles ((dgHomGluingBimodule R C D E p q).value (L.obj x) (G.obj x)) := by
  change zeroCycles (homObject R E (p.obj (L.obj x)) (q.obj (G.obj x)))
  exact closedHomEquiv R E (p.obj (L.obj x)) (q.obj (G.obj x)) (a x)

/-- 元の左右対象と同じ閉比較を保持する Hom gluing 対象。 -/
def dgHomGluingComparisonObject (x : P) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q) where
  left := L.obj x
  right := G.obj x
  gluing := dgHomGluingComparisonCycle R C D E p q L G a x

/-- 元の右関手の作用に同じ実 gluing 右作用を合成した全鎖写像。 -/
def dgHomGluingComparisonRightMap (x y : P) :
    homObject R P x y ⟶ homObject R E (p.obj (L.obj x)) (q.obj (G.obj y)) := by
  exact G.map x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D (dgHomGluingBimodule R C D E p q)
    (dgHomGluingComparisonObject R C D E p q L G a x)
    (dgHomGluingComparisonObject R C D E p q L G a y)

/-- 元の左関手の作用に同じ実 gluing 左作用を合成した全鎖写像。 -/
def dgHomGluingComparisonLeftMap (x y : P) :
    homObject R P x y ⟶ homObject R E (p.obj (L.obj x)) (q.obj (G.obj y)) := by
  exact L.map x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D (dgHomGluingBimodule R C D E p q)
    (dgHomGluingComparisonObject R C D E p q L G a x)
    (dgHomGluingComparisonObject R C D E p q L G a y)

include h in
/-- 元の全 Hom 自然性は、同じ実 gluing の左右作用の一致を与える。 -/
lemma dgHomGluingComparison_actions (x y : P) :
    dgHomGluingComparisonRightMap R C D E p q L G a x y =
      dgHomGluingComparisonLeftMap R C D E p q L G a x y := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact (dgHomGluingRightAction_apply R C D E p q
    (dgHomGluingComparisonObject R C D E p q L G a x)
    (dgHomGluingComparisonObject R C D E p q L G a y) n ((G.map x y).f n f)).trans
      ((dgClosedComparison_forward R (L.comp p) (G.comp q) a h x y n f).trans
        (dgHomGluingLeftAction_apply R C D E p q
          (dgHomGluingComparisonObject R C D E p q L G a x)
          (dgHomGluingComparisonObject R C D E p q L G a y) n ((L.map x y).f n f)).symm)

include h in
/-- 元の標的内の全 Hom 自然性は、同じ gluing augmentation の全 Hom 自然性。 -/
lemma dgHomGluingComparison_naturality (x y : P) :
    G.map x y ≫ (dgHomGluingBimodule R C D E p q).toFunctor.map (G.obj x) (G.obj y) ≫
      eHomWhiskerRight (Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D _ (dgHomGluingComparisonObject R C D E p q L G a x))
        (ForgetEnrichment.of (Complex R)
          ((dgHomGluingBimodule R C D E p q).rightAt (G.obj y))) =
    (L.comp (dgYoneda R C)).map x y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (representable R (L.obj x)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D _ (dgHomGluingComparisonObject R C D E p q L G a y)) := by
  let M := dgHomGluingBimodule R C D E p q
  let b := dgHomGluingComparisonObject R C D E p q L G a
  apply (cancel_mono (dgYonedaIso R (L.obj x) (M.rightAt (G.obj y))).hom).mp
  have hr := prependThreeEq (G.map x y) _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction_yoneda R C D M (b x) (b y))
  have hl := prependThreeEq (L.map x y) _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction_yoneda R C D M (b x) (b y))
  exact hr.trans ((dgHomGluingComparison_actions R C D E p q L G a h x y).trans hl.symm)

end SerrePositivity.KST.SConstruction
