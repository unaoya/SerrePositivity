module

public import SerrePositivity.InfinityCategories.Sheaves.Sheafify
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveLocalObjects
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
概要：指定層化の単位を全前層で固定し、層では可逆であることを示す。
方針：反射単位の成分を、前層の頂点の往復の等式で運ぶ。
使われ方：HTT 5.2.7.4・6.2.2.7、Kerodon Tag 02EH の反射像の単位。
規約：独立な同値を選ばず、同じ反射の単位を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u+1}} [Quasicategory E]

/-- 選んだ層化の頂点の表示を元の自己関手の値へ戻す。 -/
lemma functorVertex_sheafify (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (F : Presheaf C E) : functorVertex (sheafify J hJ F) =
      (sheafificationFunctor J hJ).app _ (functorVertex F) :=
  (functorVertexEquiv _ _).apply_symm_apply _

/-- 元の反射単位の同じ成分を、前層の表示の頂点へ運んだ射。 -/
def sheafifyUnitHom (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (F : Presheaf C E) : FunctorHom F (sheafify J hJ F) :=
  functorHomEvaluate (Classical.choice hJ).unit (functorVertex F) ≫
    eqToHom (congrArg HomotopyCategory.mk (functorVertex_sheafify J hJ F).symm)

/-- 同じ単位の実際のホモトピー代表。 -/
def sheafifyUnit (J : GrothendieckTopology C) (hJ : Sheafification J E)
    (F : Presheaf C E) : SSet.Homotopy F (sheafify J hJ F) :=
  functorHomHomotopy (sheafifyUnitHom J hJ F)

/-- 元の前層が層なら、指定した反射単位の成分が可逆。 -/
lemma sheafifyUnitHom_isIso_of_isSheaf (J : GrothendieckTopology C)
    (hJ : Sheafification J E) {F : Presheaf C E} (hF : IsSheaf J F) :
    IsIso (sheafifyUnitHom J hJ F) := by
  have hmem : sheafProperty J (functorVertex F) := by
    change IsSheaf J (vertexToPresheaf (functorVertex F))
    change IsSheaf J ((functorVertexEquiv _ _).symm ((functorVertexEquiv _ _) F))
    rw [Equiv.symm_apply_apply]
    exact hF
  have hlocal := (Classical.choice hJ).isLocal_inclusion ⟨functorVertex F, by
    intro v
    have hv : v = 𝟙 _ := Subsingleton.elim _ _
    simpa only [hv, op_id, CategoryTheory.Functor.map_id_apply] using hmem⟩
  haveI : IsIso (functorHomEvaluate (Classical.choice hJ).unit (functorVertex F)) := hlocal
  unfold sheafifyUnitHom
  infer_instance

/-- ホモトピー代表も同じ単位の可逆な辺を表す。 -/
lemma sheafifyUnit_isEquivalence_of_isSheaf (J : GrothendieckTopology C)
    (hJ : Sheafification J E) {F : Presheaf C E} (hF : IsSheaf J F) :
    IsInvertibleEdge (functorEdgeOfSimplicialHomotopy (sheafifyUnit J hJ F)) := by
  change IsIso (Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (functorHomHomotopy (sheafifyUnitHom J hJ F))))
  rw [functorHomHomotopy_hom]
  exact sheafifyUnitHom_isIso_of_isSheaf J hJ hF

end SerrePositivity.InfinityCategories.Sheaves
