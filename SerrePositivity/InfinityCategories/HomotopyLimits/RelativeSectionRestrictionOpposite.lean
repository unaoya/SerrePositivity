module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectedConeLimitLift
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorOpposite
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorOverIsomorphism

/-!
概要：相対切断の制限の同値性を反転と底上の全空間同型に沿って移す。
方針：元の比較射の可換性と Kan な写像空間の同値判定を使う。
規約：底と全パラメータは任意。使われ方：HTT 5.5.4.5(2) の局所辺の族の制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 相対関手空間の反転比較は、元の前合成と厳密に可換。 -/
lemma relativeFunctorOppositeIso_pre {A D E B : SSet.{u}} (p : E ⟶ B)
    (a : A ⟶ B) (i : D ⟶ A) :
    SSet.opFunctor.map (relativeFunctorPre p a i) ≫
        (relativeFunctorOppositeIso p (i ≫ a)).hom =
      (relativeFunctorOppositeIso p a).hom ≫
        relativeFunctorPre (SSet.opFunctor.map p) (SSet.opFunctor.map a)
          (SSet.opFunctor.map i) := by
  apply vertexFiber_hom_ext ((ihom D.op).map (SSet.opFunctor.map p))
    (functorVertex (SSet.opFunctor.map (i ≫ a)))
  rw [Category.assoc, relativeFunctorOppositeIso_hom_ι, ← Category.assoc,
    ← SSet.opFunctor.map_comp, relativeFunctorPre_ι, SSet.opFunctor.map_comp,
    Category.assoc, oppositeInternalHom_pre]
  have hr : relativeFunctorPre (SSet.opFunctor.map p) (SSet.opFunctor.map a)
      (SSet.opFunctor.map i) ≫ vertexFiberι ((ihom D.op).map (SSet.opFunctor.map p))
        (functorVertex (SSet.opFunctor.map (i ≫ a))) =
      vertexFiberι ((ihom A.op).map (SSet.opFunctor.map p))
        (functorVertex (SSet.opFunctor.map a)) ≫ (pre (SSet.opFunctor.map i)).app E.op :=
    relativeFunctorPre_ι (SSet.opFunctor.map p) (SSet.opFunctor.map a) (SSet.opFunctor.map i)
  simp only [Category.assoc, hr]
  simpa only [Category.assoc] using
    (congrArg (fun t ↦ t ≫ (pre (SSet.opFunctor.map i)).app E.op)
      (relativeFunctorOppositeIso_hom_ι p a)).symm

/-- Kan な相対関手空間の制限の同値性は反転により検出できる。 -/
lemma relativeFunctorPre_homotopyEquivalence_iff_op {A D E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A)
    [KanComplex (relativeFunctorSpace p a)] [KanComplex (relativeFunctorSpace p (i ≫ a))] :
    IsSimplicialHomotopyEquivalence (relativeFunctorPre p a i) ↔
      IsSimplicialHomotopyEquivalence
        (relativeFunctorPre (SSet.opFunctor.map p) (SSet.opFunctor.map a)
          (SSet.opFunctor.map i)) := by
  have hs' := kanComplex_of_iso (relativeFunctorOppositeIso p a)
  have ht' := kanComplex_of_iso (relativeFunctorOppositeIso p (i ≫ a))
  have : KanComplex (relativeFunctorSpace (SSet.opFunctor.map p)
      (SSet.opFunctor.map i ≫ SSet.opFunctor.map a)) := ht'
  rw [← oppositeKanHomotopyEquivalence_iff (relativeFunctorPre p a i)]
  have hs : IsQCatEquivalence (relativeFunctorOppositeIso p a).hom :=
    (qCatEquivalenceOfIso (relativeFunctorOppositeIso p a)).isQCatEquivalence
  have ht : IsQCatEquivalence (relativeFunctorOppositeIso p (i ≫ a)).hom :=
    (qCatEquivalenceOfIso (relativeFunctorOppositeIso p (i ≫ a))).isQCatEquivalence
  constructor
  · intro h
    have hc := h.isQCatEquivalence.comp ht
    rw [relativeFunctorOppositeIso_pre] at hc
    exact (hs.cancel_left hc).isSimplicialHomotopyEquivalence
  · intro h
    have hc := hs.comp h.isQCatEquivalence
    rw [← relativeFunctorOppositeIso_pre] at hc
    exact (ht.cancel_right hc).isSimplicialHomotopyEquivalence

/-- 相対切断の制限の同値性は、底上の全空間の同型で変わらない。 -/
lemma relativeFunctorPre_homotopyEquivalence_iff_totalIso {A D B : SSet.{u}}
    {p q : Over B} (e : p ≅ q) (a : A ⟶ B) (i : D ⟶ A)
    [KanComplex (relativeFunctorSpace p.hom a)]
    [KanComplex (relativeFunctorSpace p.hom (i ≫ a))] :
    IsSimplicialHomotopyEquivalence (relativeFunctorPre p.hom a i) ↔
      IsSimplicialHomotopyEquivalence (relativeFunctorPre q.hom a i) := by
  let es : relativeFunctorSpace p.hom a ≅ relativeFunctorSpace q.hom a :=
    (relativeFunctorOverPostFunctor a).mapIso e
  let et : relativeFunctorSpace p.hom (i ≫ a) ≅ relativeFunctorSpace q.hom (i ≫ a) :=
    (relativeFunctorOverPostFunctor (i ≫ a)).mapIso e
  have := kanComplex_of_iso es
  have := kanComplex_of_iso et
  have he : es.hom ≫ relativeFunctorPre q.hom a i =
      relativeFunctorPre p.hom a i ≫ et.hom :=
    relativeFunctorPost_pre p.hom q.hom e.hom.left e.hom.w a i
  have hs : IsQCatEquivalence (es).hom :=
    (qCatEquivalenceOfIso (es)).isQCatEquivalence
  have ht : IsQCatEquivalence (et).hom :=
    (qCatEquivalenceOfIso (et)).isQCatEquivalence
  constructor
  · intro h
    have hc := h.isQCatEquivalence.comp ht
    rw [← he] at hc
    exact (hs.cancel_left hc).isSimplicialHomotopyEquivalence
  · intro h
    have hc := hs.comp h.isQCatEquivalence
    rw [he] at hc
    exact (ht.cancel_right hc).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
