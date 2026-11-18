module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurDegreeDecomposition
public import SerrePositivity.EInfinity.BarrattEccles.Theory.RepresentationComplex
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Schur 表示の arity 分解を複体全体で読む

Berger–Moerdijk §1 の Schur 関手について、有限全単射の余極限を
arity ごとの余不変の複体の直和へ同定する。HA 3.2.4.7 の自由比較で使う。
次数ごとの商写像を指定したまま、複体の微分と余極限性を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A] (F : FiniteBijection ⥤ Complex A)

/-- 一つの arity の群作用を、余不変の複体にする。 -/
def arityCoinvariantComplex (n : ℕ) : Complex A :=
  ((Rep.coinvariantsFunctor A (ULift.{u} (Equiv.Perm (Fin n)))).mapHomologicalComplex
    (.up ℤ)).obj (representationCochainComplex (finiteBijectionComplexAction F n))

/-- 標準有限集合での値から、arity ごとの余不変の複体への指定商写像。 -/
def arityCoinvariantComplexQuotient (n : ℕ) :
    F.obj (FiniteBijection.of n) ⟶ arityCoinvariantComplex F n :=
  (representationCochainForgetIso (finiteBijectionComplexAction F n)).inv ≫
    (NatTrans.mapHomologicalComplex
      (Rep.coinvariantsMk A (ULift.{u} (Equiv.Perm (Fin n)))) (.up ℤ)).app
        (representationCochainComplex (finiteBijectionComplexAction F n))

/-- 指定商写像の各次数は、既存の arity の商写像そのもの。 -/
lemma arityCoinvariantComplexQuotient_f (n : ℕ) (i : ℤ) :
    (arityCoinvariantComplexQuotient F n).f i =
      arityDiagramQuotient (F ⋙ HomologicalComplex.eval (ModuleCat A) (.up ℤ) i) n := rfl

/-- 余不変の複体への指定商写像は、実際の置換作用を等しくする。 -/
lemma arityCoinvariantComplexQuotient_invariant (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    F.map (FiniteBijection.permutation n σ) ≫ arityCoinvariantComplexQuotient F n =
      arityCoinvariantComplexQuotient F n := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact arityDiagramQuotient_invariant
    (F ⋙ HomologicalComplex.eval (ModuleCat A) (.up ℤ) i) n σ

/-- arity ごとの余不変の複体の直和を頂点とする余錐。 -/
def arityCoinvariantComplexCocone : Cocone F :=
  Cocone.mk (∐ arityCoinvariantComplex F)
    { app X := F.map (eqToHom (FiniteBijection.of_card X).symm) ≫
        arityCoinvariantComplexQuotient F X.card ≫ Sigma.ι (arityCoinvariantComplex F) X.card
      naturality := by
        intro X Y f
        obtain rfl := FiniteBijection.object_eq_of_hom f
        obtain ⟨n, rfl⟩ : ∃ n, FiniteBijection.of n = X :=
          ⟨X.card, FiniteBijection.of_card X⟩
        rw [← FiniteBijection.homOfEquiv_equivOfHom f]
        change F.map (FiniteBijection.permutation n (FiniteBijection.equivOfHom f)) ≫ _ = _
        simp only [FiniteBijection.card_of, eqToHom_refl, F.map_id, Category.id_comp,
          ← Category.assoc, arityCoinvariantComplexQuotient_invariant]
        rfl }

/-- 複体の余錐を評価すると、既存の次数ごとの余不変の余錐に一致する。 -/
def arityCoinvariantComplexCoconeEvalIso (i : ℤ) :
    (HomologicalComplex.eval (ModuleCat A) (.up ℤ) i).mapCocone
        (arityCoinvariantComplexCocone F) ≅
      arityDiagramCocone (F ⋙ HomologicalComplex.eval (ModuleCat A) (.up ℤ) i) := by
  let E := HomologicalComplex.eval (ModuleCat A) (.up ℤ) i
  let e := PreservesCoproduct.iso E (arityCoinvariantComplex F)
  have hi (n : ℕ) : E.map (Sigma.ι (arityCoinvariantComplex F) n) ≫ e.hom =
      Sigma.ι (fun n => E.obj (arityCoinvariantComplex F n)) n :=
    (isColimitOfHasCoproductOfPreservesColimit E
      (arityCoinvariantComplex F)).comp_coconePointUniqueUpToIso_hom
     
        (coproductIsCoproduct (fun n => E.obj (arityCoinvariantComplex F n))) (Discrete.mk n)
  refine Cocone.ext e ?_
  intro X
  change E.map (F.map (eqToHom (FiniteBijection.of_card X).symm) ≫
      arityCoinvariantComplexQuotient F X.card ≫
        Sigma.ι (arityCoinvariantComplex F) X.card) ≫ e.hom = _
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, hi]
  rfl

/-- arity ごとの余不変の複体の直和は、元の図式の余極限である。 -/
def arityCoinvariantComplexIsColimit : IsColimit (arityCoinvariantComplexCocone F) :=
  HomologicalComplex.isColimitOfEval F _ fun i =>
    IsColimit.ofIsoColimit
      (arityDiagramCoconeIsColimit (F ⋙ HomologicalComplex.eval (ModuleCat A) (.up ℤ) i))
      (arityCoinvariantComplexCoconeEvalIso F i).symm

/-- 有限全単射の余極限の arity 分解は、微分を保つ複体の同型である。 -/
def arityCoinvariantComplexIso : colimit F ≅ ∐ arityCoinvariantComplex F :=
  (colimit.isColimit F).coconePointUniqueUpToIso (arityCoinvariantComplexIsColimit F)

/-- 分解同型は、元の余極限の生成元を指定商写像の後の直和包含へ送る。 -/
lemma arityCoinvariantComplexIso_ι (n : ℕ) :
    colimit.ι F (FiniteBijection.of n) ≫ (arityCoinvariantComplexIso F).hom =
      arityCoinvariantComplexQuotient F n ≫ Sigma.ι (arityCoinvariantComplex F) n := by
  simpa only [arityCoinvariantComplexIso, arityCoinvariantComplexCocone,
    colimit.cocone_ι, FiniteBijection.card_of, eqToHom_refl,
    CategoryTheory.Functor.map_id, Category.id_comp] using
    (colimit.isColimit F).comp_coconePointUniqueUpToIso_hom
    (arityCoinvariantComplexIsColimit F) (FiniteBijection.of n)

/-- 実際の Schur 複体の arity 分解。零入力と全整数次数を含む。 -/
def schurComplexArityIso (P : SymmetricSequence (Complex A)) (K : Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P).obj K ≅ ∐ arityCoinvariantComplex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K) :=
  arityCoinvariantComplexIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K)

end SerrePositivity.EInfinity
