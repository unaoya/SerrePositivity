module

public import SerrePositivity.KST.LocalizingInvariants.LocalizationHoPrecomposition

/-!
概要：元の指定辺の類を反転する通常関手を、商の h 圏へ下ろす。
方針：実 ∞ 関手の降下と FunctorIso を nerve 随伴の余単位で通常の自然同型へ戻す。
規約：nerve 随伴の可逆余単位で、元の通常関手の反転条件を転置へ移す。
使われ方：商の h 圏の通常局所化普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def nerveAdjunctFunctorIso {X : SSet.{u}} {A : Type u} [Category.{u} A]
    {f g : X ⟶ nerve A} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    ((nerveAdjunction.homEquiv X (Cat.of A)).symm f).toFunctor ≅
      ((nerveAdjunction.homEquiv X (Cat.of A)).symm g).toFunctor := by
  change (hoFunctor.map f).toFunctor ⋙ (nerveAdjunction.counit.app (Cat.of A)).toFunctor ≅
    (hoFunctor.map g).toFunctor ⋙ (nerveAdjunction.counit.app (Cat.of A)).toFunctor
  exact Functor.isoWhiskerRight e.toNatIso _

lemma nerveAdjunct_inverts {X : SSet.{u}} {A : Type u} [Category.{u} A]
    (H : hoFunctor.obj X ⥤ A) (W : Set (X _⦋1⦌))
    (hH : ∀ s ∈ W, IsIso (H.map (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (nerveAdjunction.homEquiv X (Cat.of A) H.toCatHom) W := by
  let U : X ⟶ nerve A := nerveAdjunction.homEquiv X (Cat.of A) H.toCatHom
  let eA := Cat.equivOfIso (nerveFunctorCompHoFunctorIso.app (Cat.of A))
  have hh : (hoFunctor.map U).toFunctor ⋙ eA.functor = H := by
    exact congrArg Cat.Hom.toFunctor
      ((nerveAdjunction.homEquiv X (Cat.of A)).symm_apply_apply H.toCatHom)
  intro s hs
  change IsIso (SSet.Truncated.HomotopyCategory.homMk
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map U)))
  have hm : IsIso (eA.functor.map (SSet.Truncated.HomotopyCategory.homMk
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map U)))) := by
    change IsIso (((hoFunctor.map U).toFunctor ⋙ eA.functor).map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s)))
    rw [hh]
    exact hH s hs
  exact isIso_of_fully_faithful eA.functor _

lemma localizationHo_exists_factorization_of_invertingAdjunct {X Q : SSet.{u}}
    [Quasicategory Q] (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W)
    {A : Type u} [Category.{u} A] (H : hoFunctor.obj X ⥤ A)
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (nerveAdjunction.homEquiv X (Cat.of A) H.toCatHom) W) :
    ∃ K : hoFunctor.obj Q ⥤ A, Nonempty ((hoFunctor.map F).toFunctor ⋙ K ≅ H) := by
  obtain ⟨K, ⟨e⟩⟩ := localization_exists_factorization (Y := nerve A) F W hF
    (nerveAdjunction.homEquiv X (Cat.of A) H.toCatHom) hH
  refine ⟨((nerveAdjunction.homEquiv Q (Cat.of A)).symm K).toFunctor, ⟨?_⟩⟩
  have h := nerveAdjunctFunctorIso e
  have hl := congrArg Cat.Hom.toFunctor
    (nerveAdjunction.homEquiv_naturality_left_symm (Y := Cat.of A) F K)
  have hr := congrArg Cat.Hom.toFunctor
    ((nerveAdjunction.homEquiv X (Cat.of A)).symm_apply_apply H.toCatHom)
  rw [hl, hr] at h
  exact h

lemma localizationHo_exists_factorization {X Q : SSet.{u}} [Quasicategory Q]
    (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W)
    {A : Type u} [Category.{u} A] (H : hoFunctor.obj X ⥤ A)
    (hH : ∀ s ∈ W, IsIso (H.map (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s)))) :
    ∃ K : hoFunctor.obj Q ⥤ A, Nonempty ((hoFunctor.map F).toFunctor ⋙ K ≅ H) :=
  localizationHo_exists_factorization_of_invertingAdjunct F W hF H (nerveAdjunct_inverts H W hH)

end SerrePositivity.KST.LocalizingInvariants
