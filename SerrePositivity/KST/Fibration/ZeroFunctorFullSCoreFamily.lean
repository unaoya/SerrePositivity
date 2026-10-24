module
public import SerrePositivity.KST.Fibration.ZeroFunctorLocus
public import SerrePositivity.KST.Fibration.RelativeDiagramKernel
public import SerrePositivity.KST.Fibration.SComponentExactness
public import SerrePositivity.KST.SConstruction.SExactFamilyMap
public import SerrePositivity.KST.SConstruction.SExactEnrichedFunctor
public import SerrePositivity.InfinityCategories.Stable.CurryVertexEvaluation

/-!
概要：元の零値完全関手の全族を、全 S_n から商の core S_n への実作用へ送る。
方針：全 Ar 評価で零性を検証し、同じ全パラメータ作用を core に持ち上げる。
規約：入力の全 S_n を core に縮めず、元の全自然変換と二胞体を保持する。
使われ方：商核四角形の零角比較と、指定 Verdier 上辺の全図式比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

private lemma uncurry_at_vertex {A B P : SSet.{u}} (F : P ⟶ (ihom A).obj B)
    (p : P _⦋0⦌) (f : A ⟶ B) (hp : F.app (Opposite.op ⦋0⦌) p = functorVertex f)
    (a : A _⦋0⦌) : (uncurry F).app (Opposite.op ⦋0⦌) (a, p) = f.app (Opposite.op ⦋0⦌) a := by
  have he := curry_evaluation_vertex (uncurry F) a
  rw [curry_uncurry] at he
  have h := congrArg (fun m => m.app (Opposite.op ⦋0⦌) p) he
  change (evaluateFunctorAt a).app (Opposite.op ⦋0⦌) (F.app (Opposite.op ⦋0⦌) p) = _ at h
  rw [hp, evaluateFunctorAt_functorVertex] at h
  change f.app (Opposite.op ⦋0⦌) a =
    (uncurry F).app (Opposite.op ⦋0⦌) (PinchedHom.constant a 0, p) at h
  rw [pinchedConstant_zero] at h
  exact h.symm

/-- 零値の同じ完全関手は、全 S_n の全図式を元の零図式へ送る。 -/
theorem zeroFunctor_sExactMap_values {A C : StableCategory.{u}} (F : ExactMap A C)
    (hF : IsZeroVertex (functorVertex F.hom)) (n : ℕ)
    (v : (sConstruction n A.obj) _⦋0⦌) :
    IsZeroVertex (((sExactMap n F).hom).app (Opposite.op ⦋0⦌) v) := by
  rw [sConstruction_isZeroVertex_iff_components]
  intro a
  have he := congrArg (fun m : sConstruction n A.obj ⟶ C.obj => m.app (Opposite.op ⦋0⦌) v)
    (sPostcomp_gapped_evaluate n F.hom (exactMap_preservesSData F) a)
  have hz := isZeroVertex_evaluateFunctorAt hF
    ((sComponentEvaluation A.obj n a).app (Opposite.op ⦋0⦌) v)
  rw [evaluateFunctorAt_functorVertex] at hz
  exact he.symm ▸ hz

/-- 元の零値関手の全パラメータを、元の全 S_n へ作用させる。 -/
def zeroFunctorFullSAction (A C : StableCategory.{u}) (n : ℕ) :
    sConstruction n A.obj ⊗ zeroFunctorLocus A C ⟶ sConstruction n C.obj :=
  uncurry (zeroFunctorLocusToExact A C ≫ sExactFamilyMap n A C)

/-- 同じ全作用の全頂点は、全 Ar 成分が零となる元の S_n 図式。 -/
theorem zeroFunctorFullSAction_values (A C : StableCategory.{u}) (n : ℕ)
    (v : (sConstruction n A.obj ⊗ zeroFunctorLocus A C) _⦋0⦌) :
    IsZeroVertex ((zeroFunctorFullSAction A C n).app (Opposite.op ⦋0⦌) v) := by
  rcases v with ⟨a, p⟩
  obtain ⟨F, hF⟩ := (exactFunctorVertexEquiv A C).surjective
    ((zeroFunctorLocusToExact A C).app (Opposite.op ⦋0⦌) p)
  have hz : IsZeroVertex (functorVertex F.hom) := by
    have he := congrArg (fun w => (exactFunctors A C).ι.app (Opposite.op ⦋0⦌) w) hF
    change functorVertex F.hom = p.val at he
    exact he.symm ▸ fullSubcomplexOnVertices_vertex p
  have hv : (zeroFunctorLocusToExact A C ≫ sExactFamilyMap n A C).app
      (Opposite.op ⦋0⦌) p = functorVertex (sExactMap n F).hom := by
    change (sExactFamilyMap n A C).app (Opposite.op ⦋0⦌)
      ((zeroFunctorLocusToExact A C).app (Opposite.op ⦋0⦌) p) = _
    rw [← hF, sExactFamilyMap_vertex]
  rw [zeroFunctorFullSAction, uncurry_at_vertex _ _ _ hv]
  exact zeroFunctor_sExactMap_values F hz n a

/-- 同じ全 S_n 作用を、全単体・全パラメータのまま元の core へ持ち上げる。 -/
def zeroFunctorFullSCoreAction (A C : StableCategory.{u}) (n : ℕ) :
    sConstruction n A.obj ⊗ zeroFunctorLocus A C ⟶
      (quasicategoryCore (sConstruction n C.obj) : SSet.{u}) :=
  quasicategoryCoreLift (zeroFunctorFullSAction A C n)
    (map_edge_invertible_of_zero _ (zeroFunctorFullSAction_values A C n))

/-- core に持ち上げた同じ全作用は、周囲で元の全作用そのもの。 -/
theorem zeroFunctorFullSCoreAction_ι (A C : StableCategory.{u}) (n : ℕ) :
    zeroFunctorFullSCoreAction A C n ≫ (quasicategoryCore (sConstruction n C.obj)).ι =
      zeroFunctorFullSAction A C n :=
  quasicategoryCoreLift_ι _ _

/-- 元の全零値関手族の作用は、core 持ち上げ後も全ての面・退化と可換。 -/
theorem zeroFunctorFullSCoreAction_reindex (A C : StableCategory.{u}) {m n : ℕ}
    (θ : Fin (m + 1) →o Fin (n + 1)) :
    (sMap A.obj θ ▷ zeroFunctorLocus A C) ≫ zeroFunctorFullSCoreAction A C m =
      zeroFunctorFullSCoreAction A C n ≫ quasicategoryCoreMap (sMap C.obj θ) := by
  apply (cancel_mono (quasicategoryCore (sConstruction m C.obj)).ι).1
  rw [Category.assoc, zeroFunctorFullSCoreAction_ι, Category.assoc, quasicategoryCoreMap_ι,
    ← Category.assoc, zeroFunctorFullSCoreAction_ι]
  dsimp only [zeroFunctorFullSAction]
  rw [← uncurry_pre_app, ← uncurry_natural_right]
  apply congrArg uncurry
  simp only [Category.assoc]
  rw [← sExactFamilyMap_restriction]

/-- 元の全 S• と全零値関手パラメータを保持する、同じ core 値自然変換。 -/
def zeroFunctorFullSCoreNatTrans (A C : StableCategory.{u}) :
    simplicialSConstruction A.obj ⋙ tensorRight (zeroFunctorLocus A C) ⟶
      simplicialSConstruction C.obj ⋙ quasicategoryCoreFunctor where
  app n := zeroFunctorFullSCoreAction A C n.unop.len
  naturality {_ _} θ := zeroFunctorFullSCoreAction_reindex A C θ.unop.toOrderHom

/-- 元の零値関手の全族による、全 S_n から core S_n への実関手族。 -/
def zeroFunctorFullSCoreFamily (A C : StableCategory.{u}) (n : ℕ) :
    zeroFunctorLocus A C ⟶ (ihom (sConstruction n A.obj)).obj
      (quasicategoryCore (sConstruction n C.obj) : SSet.{u}) :=
  curry (zeroFunctorFullSCoreAction A C n)

/-- core 包含後は、同じ元の全 S_n の全パラメータ作用を厳密に回収する。 -/
theorem zeroFunctorFullSCoreFamily_ι (A C : StableCategory.{u}) (n : ℕ) :
    zeroFunctorFullSCoreFamily A C n ≫
        (ihom (sConstruction n A.obj)).map (quasicategoryCore (sConstruction n C.obj)).ι =
      zeroFunctorLocusToExact A C ≫ sExactFamilyMap n A C := by
  rw [zeroFunctorFullSCoreFamily, ← curry_natural_right]
  rw [zeroFunctorFullSCoreAction, quasicategoryCoreLift_ι, zeroFunctorFullSAction, curry_uncurry]

end SerrePositivity.KST.Fibration
