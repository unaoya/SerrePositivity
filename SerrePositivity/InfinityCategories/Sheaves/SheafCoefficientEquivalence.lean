module

public import SerrePositivity.InfinityCategories.Sheaves.SheafLimitClosure
public import SerrePositivity.InfinityCategories.Sheaves.SheafEquivalence
public import SerrePositivity.InfinityCategories.Sheaves.SheafGlobalSectionsFamily
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullSubcomplexRestrictionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorComposition

/-!
概要：係数の同じ指定同値を、層の全部分準圏へ制限する。
方針：元の篩錐の極限性の保存反映と、全部分圏の同値判定を組み合わせる。
使われ方：HA §1.1.3、Kerodon §4.5.1（Tag 01DQ）の係数の同値に沿う層の移送。
規約：全前層関手との可換式を等式として保持し、点ごとの同値へ弱めない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C]
variable {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]

/-- 係数関手による後合成は、元の関手頂点の読み戻しと可換。 -/
lemma vertexToPresheaf_postcomp (G : E ⟶ B) (v : (PresheafCat C E) _⦋0⦌) :
    vertexToPresheaf (((ihom (presheafShape C)).map G).app _ v) =
      vertexToPresheaf v ≫ G := by
  obtain ⟨F, rfl⟩ := (functorVertexEquiv _ _).surjective v
  change (functorVertexEquiv _ _).symm ((functorVertexEquiv _ _) (F ≫ G)) =
    (functorVertexEquiv _ _).symm ((functorVertexEquiv _ _) F) ≫ G
  simp only [Equiv.symm_apply_apply]

/-- 係数の指定同値は、元の層条件を保存し反映する。 -/
lemma isSheaf_postcomp_equivalence_iff (J : GrothendieckTopology C)
    (e : QCatEquivalence E B) (F : Presheaf C E) :
    IsSheaf J (F ≫ e.hom) ↔ IsSheaf J F := by
  constructor
  · intro h
    have h' := h.postcomp_of_equivalence e.symm
    have a : FunctorIso ((F ≫ e.hom) ≫ e.inv) F := by
      simpa only [Category.assoc, Category.comp_id] using e.homInvIso.precomp F
    exact h'.of_functorIso a
  · exact fun h ↦ h.postcomp_of_equivalence e

/-- 全後合成関手の頂点での、元の層条件の保存反映。 -/
lemma sheafProperty_postcomp_equivalence_iff (J : GrothendieckTopology C)
    (e : QCatEquivalence E B) (v : (PresheafCat C E) _⦋0⦌) :
    sheafProperty J (((ihom (presheafShape C)).map e.hom).app _ v) ↔ sheafProperty J v := by
  dsimp only [sheafProperty]
  rw [vertexToPresheaf_postcomp]
  exact isSheaf_postcomp_equivalence_iff J e _

/-- 同じ指定係数同値の全後合成を層圏へ制限する。 -/
def postcomposeSheafFunctor (J : GrothendieckTopology C) (e : QCatEquivalence E B) :
    SheafCat J E ⟶ SheafCat J B :=
  fullSubcomplexLift (sheafProperty (E := B) J)
    (sheafInclusion (E := E) J ≫ (ihom (presheafShape C)).map e.hom)
    (fun x ↦ (sheafProperty_postcomp_equivalence_iff J e x.val).mpr
      (fullSubcomplexOnVertices_vertex x))

/-- 係数移送は、元の全前層関手への包含と厳密に可換。 -/
lemma postcomposeSheafFunctor_comp (J : GrothendieckTopology C) (e : QCatEquivalence E B) :
    postcomposeSheafFunctor J e ≫ sheafInclusion J =
      sheafInclusion J ≫ (ihom (presheafShape C)).map e.hom :=
  fullSubcomplexLift_ι _ _ _

/-- 同じ指定係数同値は、層の全部分準圏の同値を与える。 -/
theorem postcomposeSheafFunctor_isQCatEquivalence (J : GrothendieckTopology C)
    (e : QCatEquivalence E B) : IsQCatEquivalence (postcomposeSheafFunctor J e) := by
  apply isQCatEquivalence_fullSubcomplexRestriction
    (sheafProperty (E := E) J) (sheafProperty (E := B) J)
    (fun h ↦ sheafProperty_iff_of_vertexIso J h)
    ((ihom (presheafShape C)).map e.hom) (e.postcompose _).isQCatEquivalence
    _ (postcomposeSheafFunctor_comp J e)
  intro x hx
  exact (sheafProperty_postcomp_equivalence_iff J e x).mp hx

end SerrePositivity.InfinityCategories.Sheaves
