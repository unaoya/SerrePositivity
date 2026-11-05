module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Infinity.ExactEnrichment
public import SerrePositivity.InfinityCategories.F1.Coherent.ArrowData

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Stable.Infinity
open SerrePositivity.KST.LocalizingInvariants

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

end SerrePositivity.InfinityCategories.Stable.Infinity

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableInfinity := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableQCat := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.exactHomEquiv (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactHomEquiv := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.exactHomEquiv

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactHomEquiv_ι := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.exactHomEquiv_ι

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableCategory_simplicialCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_simplicialCategory := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableCategory_simplicialCategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableInfinity_quasicategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableInfinity_quasicategory := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableInfinity_quasicategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableObject (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableObject := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableObject

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableObject_vertex := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableObject_vertex

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableQCat_category (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableQCat_category := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableQCat_category

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableQCat_sHom_kanComplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableQCat_sHom_kanComplex := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableQCat_sHom_kanComplex

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableQCat_simplicialCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableQCat_simplicialCategory := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableQCat_simplicialCategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableVertex := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableVertex_object := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableVertex_object

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactHomEquiv.eq_1 := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.exactHomEquiv.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_simplicialCategory._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableCategory_simplicialCategory._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_simplicialCategory._proof_3 := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableCategory_simplicialCategory._proof_3

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableQCat_category._aux_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableQCat_category._aux_1 := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableQCat_category._aux_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableQCat_category._aux_3 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableQCat_category._aux_3 := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableQCat_category._aux_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableQCat_category._proof_5 := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableQCat_category._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableQCat_category._proof_6 := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableQCat_category._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableQCat_category._proof_7 := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableQCat_category._proof_7
