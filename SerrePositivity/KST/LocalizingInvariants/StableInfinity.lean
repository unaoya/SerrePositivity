module

public import SerrePositivity.KST.LocalizingInvariants.ExactEnrichment
public import SerrePositivity.InfinityCategories.F1.CoherentArrowData

/-!
概要：安定 ∞ 圏と完全関手の ∞ 圏。
方針：完全関手 ∞ 圏の core を豊穣 Hom とし、局所 Kan な単体的圏の nerve を取る。
規約：通常 nerve で高次の自然同値を失わない。使われ方：K-5 の Sp 値 ∞ 関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

private lemma unitVertex_comp {X Y : SSet.{u}} (f : (𝟙_ SSet.{u}) ⟶ X) (g : X ⟶ Y) :
    SSet.unitHomEquiv Y (f ≫ g) =
      g.app (Opposite.op ⦋0⦌) (SSet.unitHomEquiv X f) := rfl

/-- 完全関手の通常射と豊穣 Hom の単位からの射の同値。 -/
def exactHomEquiv {A B : StableCategory.{u}} :
    (A ⟶ B) ≃ ((𝟙_ SSet.{u}) ⟶ (exactFunctors A B : SSet.{u})) :=
  (exactFunctorVertexEquiv A B).trans (SSet.unitHomEquiv _).symm

/-- 豊穣射の包含は元の関手の curry に一致する。 -/
lemma exactHomEquiv_ι {A B : StableCategory.{u}} (F : A ⟶ B) :
    exactHomEquiv F ≫ (exactFunctors A B).ι = curry' F.hom := by
  apply (SSet.unitHomEquiv _).injective
  rw [unitVertex_comp]
  simp only [exactHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- 完全関手の通常の恒等・合成と単体的合成の整合性。 -/
instance stableCategory_simplicialCategory : SimplicialCategory StableCategory.{u} where
  homEquiv := exactHomEquiv
  homEquiv_id A := by
    apply (cancel_mono (exactFunctors A A).ι).1
    change exactHomEquiv (𝟙 A) ≫ (exactFunctors A A).ι =
      exactIdentity A ≫ (exactFunctors A A).ι
    rw [exactHomEquiv_ι (𝟙 A)]
    exact (curry'_id A.obj).trans (exactIdentity_ι A).symm
  homEquiv_comp {A B C} F G := by
    apply (cancel_mono (exactFunctors A C).ι).1
    change exactHomEquiv (F ≫ G) ≫ (exactFunctors A C).ι =
      ((λ_ (𝟙_ SSet.{u})).inv ≫ (exactHomEquiv F ⊗ₘ exactHomEquiv G) ≫
        exactComposition A B C) ≫ (exactFunctors A C).ι
    rw [exactHomEquiv_ι]
    simp only [Category.assoc, exactComposition_ι]
    have h := curry'_comp (C := SSet.{u}) F.hom G.hom
    change curry' (F.hom ≫ G.hom) = _
    rw [h]
    simp only [← exactHomEquiv_ι F, ← exactHomEquiv_ι G,
      ← tensorHom_comp_tensorHom, Category.assoc]

/-- core によって自然同値だけを残した単体的圏。 -/
def StableQCat : Type (u + 1) :=
  TransportEnrichment quasicategoryCoreFunctor.{u} StableCategory.{u}

instance stableQCat_category : Category.{u} StableQCat.{u} :=
  inferInstanceAs (Category.{u}
    (TransportEnrichment quasicategoryCoreFunctor.{u} StableCategory.{u}))

instance stableQCat_simplicialCategory : SimplicialCategory StableQCat.{u} :=
  TransportEnrichment.enrichedOrdinaryCategory StableCategory.{u} quasicategoryCoreFunctor.{u}
    quasicategoryCoreUnitHomEquiv quasicategoryCoreUnitHomEquiv_eq

instance stableQCat_sHom_kanComplex (A B : StableQCat.{u}) :
    KanComplex (SimplicialCategory.sHom A B) :=
  inferInstanceAs (KanComplex
    (quasicategoryCore (exactFunctors A B : SSet.{u}) : SSet.{u}))

/-- 小さい安定 ∞ 圏と完全関手の ∞ 圏。 -/
def StableInfinity : SSet.{u + 1} := SimplicialNerve StableQCat.{u}

instance stableInfinity_quasicategory : Quasicategory StableInfinity.{u} :=
  Coherent.simplicialNerve_quasicategory StableQCat.{u}

/-- 元の安定対象に対応する実際の頂点。 -/
def stableVertex (A : StableCategory.{u}) : StableInfinity.{u} _⦋0⦌ :=
  coherentNerveVertex (C := StableQCat.{u}) A

/-- 任意の頂点から束ねた安定対象を復元する。 -/
def stableObject (a : StableInfinity.{u} _⦋0⦌) : StableCategory.{u} :=
  coherentNerveObject (C := StableQCat.{u}) a

lemma stableObject_vertex (A : StableCategory.{u}) : stableObject (stableVertex A) = A := rfl

lemma stableVertex_object (a : StableInfinity.{u} _⦋0⦌) : stableVertex (stableObject a) = a :=
  coherentNerveVertex_object (C := StableQCat.{u}) a

end SerrePositivity.KST.LocalizingInvariants
