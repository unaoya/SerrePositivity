module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativePullbackPointedIsoLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorSpace
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseMorphismDown
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.UniverseEdgeTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerHom
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseFunctorIso

/-!
概要：指定した関手同型を元の宇宙へ戻す。
方針：内部 Hom の厳密な宇宙同型と上げ下げの関手で、元の射の類を保持する。
規約：HTT §3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）の指定比較の移送。
使われ方：R04.2 の元の底変換の同型。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

private abbrev loweredHo {A X : SSet.{u}} :=
  mapHomotopyCategory (uliftFunctorSpaceIso.{u, v} A X).inv ⋙
    downFunctor.{u, v} ((ihom A).obj X)

private def lowerFunctorIso {A X : SSet.{u}}
    {f g : (SSet.uliftFunctor.{v, u}).obj A ⟶ (SSet.uliftFunctor.{v, u}).obj X}
    (i : FunctorIso f g) :
    FunctorIso (uliftMorphismDown f) (uliftMorphismDown g) :=
  (loweredHo (A := A) (X := X)).mapIso i

private lemma lowerFunctorIso_rep {A X : SSet.{u}} [Quasicategory (SSet.uliftFunctor.{v, u}.obj X)]
    {f g : (SSet.uliftFunctor.{v, u}).obj A ⟶ (SSet.uliftFunctor.{v, u}).obj X}
    (i : FunctorIso f g)
    (e : Truncated.Edge (X := (truncation 2).obj
      ((ihom (SSet.uliftFunctor.{v, u}.obj A)).obj (SSet.uliftFunctor.{v, u}.obj X)))
      (functorVertex f) (functorVertex g)) (he : Truncated.HomotopyCategory.homMk e = i.hom) :
    (lowerFunctorIso i).hom =
    Truncated.HomotopyCategory.homMk
      (down (e.map ((truncation 2).map (uliftFunctorSpaceIso.{u, v} A X).inv))) := by
  change (downFunctor.{u, v} ((ihom A).obj X)).map
    ((mapHomotopyCategory (uliftFunctorSpaceIso.{u, v} A X).inv).map i.hom) = _
  rw [← he]
  simp only [mapHomotopyCategory, Truncated.mapHomotopyCategory_homMk,
    downFunctor]
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

private abbrev raisedHo {A X : SSet.{u}} :=
  upFunctor.{u, v} ((ihom A).obj X) ⋙
    mapHomotopyCategory (uliftFunctorSpaceIso.{u, v} A X).hom

private def raiseFunctorIso {A X : SSet.{u}} {f g : A ⟶ X} (i : FunctorIso f g) :
    FunctorIso ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g) :=
  (raisedHo (A := A) (X := X)).mapIso i

private lemma raiseFunctorIso_rep {A X : SSet.{u}} {f g : A ⟶ X}
    (i : FunctorIso f g) (e : Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
      (functorVertex f) (functorVertex g)) (he : Truncated.HomotopyCategory.homMk e = i.hom) :
    (raiseFunctorIso.{u, v} i).hom = Truncated.HomotopyCategory.homMk
      ((up.{u, v} e).map ((truncation 2).map (uliftFunctorSpaceIso.{u, v} A X).hom)) := by
  change (mapHomotopyCategory (uliftFunctorSpaceIso.{u, v} A X).hom).map
    ((upFunctor.{u, v} ((ihom A).obj X)).map i.hom) = _
  rw [← he]
  change (mapHomotopyCategory (uliftFunctorSpaceIso.{u, v} A X).hom).map
    ((upFunctor.{u, v} ((ihom A).obj X)).map (Truncated.HomotopyCategory.homMk e)) = _
  have h : (upFunctor.{u, v} ((ihom A).obj X)).map
      (Truncated.HomotopyCategory.homMk e) =
        Truncated.HomotopyCategory.homMk (up.{u, v} e) := by
    change 𝟙 _ ≫ _ = _
    exact Category.id_comp _
  rw [h]
  rfl

private lemma raise_eq_ulift {A X : SSet.{u}} [Quasicategory X]
    {f g : A ⟶ X} (i : FunctorIso f g) :
    raiseFunctorIso.{u, v} i = functorIso_ulift.{u, v} i := by
  apply Iso.ext
  rw [raiseFunctorIso_rep i i.edge i.edge_homMk]
  change _ = Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (liftSimplicialHomotopy.{u, v} i.simplicialHomotopy))
  congr 1
  apply Truncated.Edge.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro x
  let t : ((ihom A).obj X) _⦋1⦌ := i.edge.edge
  change ULift.up (t.app n α x.down) = ULift.up
    (((SSet.yonedaEquiv.symm t).app n (SSet.stdSimplex.objEquiv.symm α.unop)).app n
      (𝟙 n) x.down)
  rw [SSet.yonedaEquiv_symm_app, Equiv.apply_symm_apply]
  apply congrArg ULift.up
  change t.app n α x.down = t.app n (α ≫ 𝟙 n) x.down
  rw [Category.comp_id]

private def lowerLiftedIso {A X : SSet.{u}} (f g : A ⟶ X)
    (i : FunctorIso ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g)) :
    FunctorIso f g := by
  have h := @lowerFunctorIso.{u, v} A X _ _ i
  change FunctorIso f g at h
  exact h

private lemma raise_lower {A X : SSet.{u}} [Quasicategory X]
    (f g : A ⟶ X)
    (i : FunctorIso ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g)) :
    raiseFunctorIso.{u, v} (lowerLiftedIso f g i) = i := by
  apply Iso.ext
  let l := lowerLiftedIso f g i
  let d : Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
      (functorVertex f) (functorVertex g) :=
    down (i.edge.map ((truncation 2).map (uliftFunctorSpaceIso.{u, v} A X).inv))
  have hd : Truncated.HomotopyCategory.homMk d = l.hom :=
    (lowerFunctorIso_rep i i.edge i.edge_homMk).symm
  change (raiseFunctorIso.{u, v} l).hom = i.hom
  rw [raiseFunctorIso_rep l d hd, ← i.edge_homMk]
  congr 1

private lemma lower_raise {A X : SSet.{u}} [Quasicategory X]
    {f g : A ⟶ X} (i : FunctorIso f g) :
    @lowerFunctorIso.{u, v} A X ((SSet.uliftFunctor.{v, u}).map f)
      ((SSet.uliftFunctor.{v, u}).map g) (raiseFunctorIso.{u, v} i) = i := by
  apply Iso.ext
  let l := raiseFunctorIso.{u, v} i
  let d : Truncated.Edge (X := (truncation 2).obj
      ((ihom (SSet.uliftFunctor.{v, u}.obj A)).obj (SSet.uliftFunctor.{v, u}.obj X)))
      (functorVertex ((SSet.uliftFunctor.{v, u}).map f))
      (functorVertex ((SSet.uliftFunctor.{v, u}).map g)) :=
    (up.{u, v} i.edge).map ((truncation 2).map (uliftFunctorSpaceIso.{u, v} A X).hom)
  have hd : Truncated.HomotopyCategory.homMk d = l.hom :=
    (raiseFunctorIso_rep i i.edge i.edge_homMk).symm
  change (lowerFunctorIso (A := A) (X := X) l).hom = i.hom
  rw [lowerFunctorIso_rep l d hd, ← i.edge_homMk]
  congr 1

private lemma lower_post {A X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : (SSet.uliftFunctor.{v, u}).obj A ⟶ (SSet.uliftFunctor.{v, u}).obj X}
    (i : FunctorIso f g) (q : X ⟶ Y) :
    lowerFunctorIso (i.postcomp ((SSet.uliftFunctor.{v, u}).map q)) =
      (lowerFunctorIso i).postcomp q := by
  apply Iso.ext
  let k : Truncated.Edge (X := (truncation 2).obj
      ((ihom (SSet.uliftFunctor.{v, u}.obj A)).obj (SSet.uliftFunctor.{v, u}.obj Y)))
      (functorVertex (f ≫ (SSet.uliftFunctor.{v, u}).map q))
      (functorVertex (g ≫ (SSet.uliftFunctor.{v, u}).map q)) :=
    i.edge.map ((truncation 2).map ((ihom _).map ((SSet.uliftFunctor.{v, u}).map q)))
  have hk : Truncated.HomotopyCategory.homMk k = (i.postcomp ((SSet.uliftFunctor.{v, u}).map q)).hom := by
    rw [functorIso_postcomp_hom, ← i.edge_homMk]
    rfl
  rw [lowerFunctorIso_rep _ k hk, functorIso_postcomp_hom,
    lowerFunctorIso_rep i i.edge i.edge_homMk]
  simp only [mapHomotopyCategory, Truncated.mapHomotopyCategory_homMk]
  congr 1

private lemma lower_pre {A X Y : SSet.{u}} [Quasicategory Y]
    {f g : (SSet.uliftFunctor.{v, u}).obj X ⟶ (SSet.uliftFunctor.{v, u}).obj Y}
    (i : FunctorIso f g) (q : A ⟶ X) :
    lowerFunctorIso (i.precomp ((SSet.uliftFunctor.{v, u}).map q)) =
      (lowerFunctorIso i).precomp q := by
  apply Iso.ext
  let k : Truncated.Edge (X := (truncation 2).obj
      ((ihom (SSet.uliftFunctor.{v, u}.obj A)).obj (SSet.uliftFunctor.{v, u}.obj Y)))
      (functorVertex ((SSet.uliftFunctor.{v, u}).map q ≫ f))
      (functorVertex ((SSet.uliftFunctor.{v, u}).map q ≫ g)) :=
    i.edge.map ((truncation 2).map ((pre ((SSet.uliftFunctor.{v, u}).map q)).app _))
  have hk : Truncated.HomotopyCategory.homMk k = (i.precomp ((SSet.uliftFunctor.{v, u}).map q)).hom := by
    rw [functorIso_precomp_hom, ← i.edge_homMk]
    rfl
  rw [lowerFunctorIso_rep _ k hk, functorIso_precomp_hom,
    lowerFunctorIso_rep i i.edge i.edge_homMk]
  simp only [mapHomotopyCategory, Truncated.mapHomotopyCategory_homMk]
  congr 1

private lemma lower_heq {A X : SSet.{u}}
    {f g f' g' : (SSet.uliftFunctor.{v, u}).obj A ⟶ (SSet.uliftFunctor.{v, u}).obj X}
    (i : FunctorIso f g) (j : FunctorIso f' g')
    (hf : f = f') (hg : g = g') (h : HEq i j) :
    HEq (lowerFunctorIso i) (lowerFunctorIso j) := by
  subst f' g'
  rw [eq_of_heq h]

/-- 指定した持ち上げを、その底の指定同型とともに元の宇宙へ戻す。 -/
@[cite HTT "3.3.2" (partial := special)
  "同じnative引き戻しの指定同型を宇宙の往復に沿って保持する法則。"]
lemma nativePullbackLift_descend_specified :
    ∀ {E B K : SSet.{u}} [Quasicategory B] [Quasicategory K] [Quasicategory E]
 (p : E ⟶ B) [LeftFibration p]
 (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))
 {f g : K ⟶ B} (e : FunctorIso f g),
let U := SSet.uliftFunctor.{u + 1, u}
∀ (a : pullback p f ⟶ pullback p g)
 (ha : a ≫ pullback.snd p g = pullback.snd p f)
 (L : FunctorIso (U.map (pullback.fst p f)) (U.map (a ≫ pullback.fst p g)))
 (hL : HEq (L.postcomp (U.map p))
   ((functorIso_ulift.{u, u + 1} e).precomp (U.map (pullback.snd p f)))),
 ∃ l : FunctorIso (pullback.fst p f) (a ≫ pullback.fst p g),
   HEq (functorIso_ulift.{u, u + 1} l) L ∧
   HEq (l.postcomp p) (e.precomp (pullback.snd p f)) := by
  intro E B K hB hK hE p hp R f g e
  dsimp only
  intro a ha L hL
  let U := SSet.uliftFunctor.{u + 1, u}
  let l : FunctorIso (pullback.fst p f) (a ≫ pullback.fst p g) :=
    lowerLiftedIso (pullback.fst p f) (a ≫ pullback.fst p g) L
  have hl : functorIso_ulift.{u, u + 1} l = L :=
    (raise_eq_ulift.{u, u + 1} l).symm.trans (raise_lower (pullback.fst p f) (a ≫ pullback.fst p g) L)
  have h₀ : U.map (pullback.fst p f) ≫ U.map p =
      U.map (pullback.snd p f) ≫ U.map f := by
    rw [← U.map_comp, ← U.map_comp, pullback.condition]
  have h₁ : U.map (a ≫ pullback.fst p g) ≫ U.map p =
      U.map (pullback.snd p f) ≫ U.map g := by
    rw [← U.map_comp, ← U.map_comp, Category.assoc, pullback.condition,
      ← Category.assoc, ha]
  refine ⟨l, heq_of_eq hl, ?_⟩
  have h := lower_heq (L.postcomp (U.map p))
    ((functorIso_ulift.{u, u + 1} e).precomp (U.map (pullback.snd p f))) h₀ h₁ hL
  rw [lower_post L p, lower_pre _ (pullback.snd p f), ← raise_eq_ulift e,
    lower_raise e] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
