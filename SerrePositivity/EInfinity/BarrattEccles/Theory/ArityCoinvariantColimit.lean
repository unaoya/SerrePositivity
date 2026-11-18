module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Schur
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# 有限全単射の図式の余極限

## 概要
Berger–Moerdijk §1 の Schur 関手の次数成分で、arity ごとの余不変を取る。

## 方針
標準有限集合の自己同型を置換群として読み、その余不変を arity ごとに直和する。

## 規約
群の左作用と、合成の順序の反転を照合する。

## 使われ方
Barratt–Eccles の Schur 表示の次数ごとの基底。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits

variable {A : Type u} [CommRing A] (F : FiniteBijection ⥤ ModuleCat.{u} A)

/-- The representation on the value at the standard object of a fixed arity. -/
def arityDiagramRepresentation (n : ℕ) :
    Representation A (ULift.{u} (Equiv.Perm (Fin n))) (F.obj (FiniteBijection.of n)) where
  toFun σ := (F.map (FiniteBijection.permutation n σ.down)).hom
  map_one' := by
    change (F.map (FiniteBijection.permutation n 1)).hom = _
    rw [FiniteBijection.permutation_one, F.map_id]
    rfl
  map_mul' σ τ := by
    change (F.map (FiniteBijection.permutation n (σ.down * τ.down))).hom = _
    rw [FiniteBijection.permutation_mul, F.map_comp]
    rfl

/-- The coinvariants in one arity. -/
abbrev arityDiagramCoinvariants (n : ℕ) :=
  ModuleCat.of A (arityDiagramRepresentation F n).Coinvariants

/-- The quotient map to the coinvariants in one arity. -/
def arityDiagramQuotient (n : ℕ) :
    F.obj (FiniteBijection.of n) ⟶ arityDiagramCoinvariants F n :=
  ModuleCat.ofHom (Representation.Coinvariants.mk (arityDiagramRepresentation F n))

lemma arityDiagramQuotient_invariant (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    F.map (FiniteBijection.permutation n σ) ≫ arityDiagramQuotient F n =
      arityDiagramQuotient F n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Representation.Coinvariants.mk_self_apply (arityDiagramRepresentation F n) ⟨σ⟩ x

/-- The cocone from the coproduct of arity coinvariants. -/
def arityDiagramCocone : Cocone F :=
  Cocone.mk (∐ (arityDiagramCoinvariants F))
    { app X := F.map (eqToHom (FiniteBijection.of_card X).symm) ≫
        arityDiagramQuotient F X.card ≫ Sigma.ι (arityDiagramCoinvariants F) X.card
      naturality := by
        intro X Y f
        obtain rfl := FiniteBijection.object_eq_of_hom f
        obtain ⟨n, rfl⟩ : ∃ n, FiniteBijection.of n = X :=
          ⟨X.card, FiniteBijection.of_card X⟩
        simp only [Functor.const_obj_map]
        rw [← FiniteBijection.homOfEquiv_equivOfHom f]
        change F.map (FiniteBijection.permutation n (FiniteBijection.equivOfHom f)) ≫ _ = _
        simp only [FiniteBijection.card_of, eqToHom_refl, F.map_id, Category.id_comp,
          ← Category.assoc, arityDiagramQuotient_invariant]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        rfl }

/-- The component of a cocone descends to the arity coinvariants. -/
def arityDiagramDesc (s : Cocone F) (n : ℕ) : arityDiagramCoinvariants F n ⟶ s.pt :=
  ModuleCat.ofHom (Representation.Coinvariants.lift (arityDiagramRepresentation F n)
    (s.ι.app (FiniteBijection.of n)).hom (by
      intro σ
      have h := congrArg ModuleCat.Hom.hom (s.w (FiniteBijection.permutation n σ.down))
      exact h))

lemma arityDiagramQuotient_desc (s : Cocone F) (n : ℕ) :
    arityDiagramQuotient F n ≫ arityDiagramDesc F s n = s.ι.app (FiniteBijection.of n) := by
  apply ModuleCat.hom_ext
  rfl

/-- The arity coinvariant cocone is colimiting. -/
def arityDiagramCoconeIsColimit : IsColimit (arityDiagramCocone F) where
  desc s := Sigma.desc (arityDiagramDesc F s)
  fac s X := by
    obtain ⟨n, rfl⟩ : ∃ n, FiniteBijection.of n = X :=
      ⟨X.card, FiniteBijection.of_card X⟩
    change (_ ≫ _ ≫ Sigma.ι _ n) ≫ _ = _
    simp only [eqToHom_refl, F.map_id, Category.id_comp, Category.assoc,
      Sigma.ι_comp_desc]
    exact arityDiagramQuotient_desc F s n
  uniq s f hf := by
    apply Sigma.hom_ext
    intro n
    rw [Sigma.ι_comp_desc]
    apply ModuleCat.hom_ext
    apply Representation.Coinvariants.hom_ext
    have h := hf (FiniteBijection.of n)
    have h' : arityDiagramQuotient F n ≫ (Sigma.ι (arityDiagramCoinvariants F) n ≫ f) =
        s.ι.app (FiniteBijection.of n) := by
      simpa only [arityDiagramCocone, FiniteBijection.card_of, eqToHom_refl, F.map_id,
        Category.id_comp, Category.assoc] using h
    exact congrArg ModuleCat.Hom.hom (h'.trans (arityDiagramQuotient_desc F s n).symm)

/-- The degree of the actual Schur complex is the coproduct of the arity coinvariants. -/
def schurDegreeArityIso (P : SymmetricSequence (DifferentialGraded.Complex A))
    (K : DifferentialGraded.Complex A) (i : ℤ) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P).obj K).X i ≅
      ∐ (arityDiagramCoinvariants
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K ⋙ HomologicalComplex.eval (ModuleCat A) (.up ℤ) i)) := by
  let E := HomologicalComplex.eval (ModuleCat A) (.up ℤ) i
  let F := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K
  exact preservesColimitIso E F ≪≫
    (colimit.isColimit (F ⋙ E)).coconePointUniqueUpToIso
      (arityDiagramCoconeIsColimit (F ⋙ E))

end SerrePositivity.EInfinity
