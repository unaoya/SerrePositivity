module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.ExactEnrichment
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ArrowData

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity
open _root_.SerrePositivity.KST.LocalizingInvariants

private lemma unitVertex_comp {X Y : SSet.{u}} (f : (𝟙_ SSet.{u}) ⟶ X) (g : X ⟶ Y) :
    SSet.unitHomEquiv Y (f ≫ g) =
      g.app (Opposite.op ⦋0⦌) (SSet.unitHomEquiv X f) := rfl

/-- 完全関手の通常射と豊穣 Hom の単位からの射の同値。 -/
def exactHomEquiv {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} :
    (A ⟶ B) ≃ ((𝟙_ SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u})) :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv A B).trans (SSet.unitHomEquiv _).symm

/-- 豊穣射の包含は元の関手の curry に一致する。 -/
lemma exactHomEquiv_ι {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv F ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B).ι = curry' F.hom := by
  apply (SSet.unitHomEquiv _).injective
  rw [unitVertex_comp]
  simp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- 完全関手の通常の恒等・合成と単体的合成の整合性。 -/
instance stableCategory_simplicialCategory : SimplicialCategory _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} where
  homEquiv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv
  homEquiv_id A := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A A).ι).1
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv (𝟙 A) ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A A).ι =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactIdentity A ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A A).ι
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv_ι (𝟙 A)]
    exact (curry'_id A.obj).trans (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactIdentity_ι A).symm
  homEquiv_comp {A B C} F G := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C).ι).1
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv (F ≫ G) ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C).ι =
      ((λ_ (𝟙_ SSet.{u})).inv ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv F ⊗ₘ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv G) ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactComposition A B C) ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C).ι
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv_ι]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactComposition_ι]
    have h := curry'_comp (C := SSet.{u}) F.hom G.hom
    change curry' (F.hom ≫ G.hom) = _
    rw [h]
    simp only [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv_ι F, ← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv_ι G,
      ← tensorHom_comp_tensorHom, Category.assoc]

/-- core によって自然同値だけを残した単体的圏。 -/
def StableQCat : Type (u + 1) :=
  TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}

instance stableQCat_category : Category.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} :=
  inferInstanceAs (Category.{u}
    (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}))

instance stableQCat_simplicialCategory : SimplicialCategory _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} :=
  TransportEnrichment.enrichedOrdinaryCategory _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u}
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv_eq

instance stableQCat_sHom_kanComplex (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    KanComplex (SimplicialCategory.sHom A B) :=
  inferInstanceAs (KanComplex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u}) : SSet.{u}))

/-- 小さい安定 ∞ 圏と完全関手の ∞ 圏。 -/
def StableInfinity : SSet.{u + 1} := SimplicialNerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}

instance stableInfinity_quasicategory : Quasicategory _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}

/-- 元の安定対象に対応する実際の頂点。 -/
def stableVertex (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A

/-- 任意の頂点から束ねた安定対象を復元する。 -/
def stableObject (a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) a

lemma stableObject_vertex (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex A) = A := rfl

lemma stableVertex_object (a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject a) = a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) a

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableInfinity := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.StableQCat := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactHomEquiv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactHomEquiv_ι := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv_ι

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableCategory_simplicialCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_simplicialCategory := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableCategory_simplicialCategory

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableInfinity_quasicategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableInfinity_quasicategory := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableInfinity_quasicategory

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableObject := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableObject_vertex := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_category (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableQCat_category := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_category

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_sHom_kanComplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableQCat_sHom_kanComplex := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_sHom_kanComplex

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_simplicialCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableQCat_simplicialCategory := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_simplicialCategory

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableVertex := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableVertex_object := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex_object

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exactHomEquiv.eq_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_simplicialCategory._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableCategory_simplicialCategory._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableCategory_simplicialCategory._proof_3 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableCategory_simplicialCategory._proof_3

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_category._aux_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableQCat_category._aux_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_category._aux_1

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_category._aux_3 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableQCat_category._aux_3 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_category._aux_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableQCat_category._proof_5 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_category._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableQCat_category._proof_6 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_category._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.stableQCat_category._proof_7 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableQCat_category._proof_7
