module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorRestrictedYoneda
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorShiftIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedRepresentableOperations
public import SerrePositivity.DifferentialGraded.Category.Tensor
/-!
概要：重複を許す任意の小さい加群ラベル族について制限 Yoneda と shift を比較する。
方針：全 Hom を実加群から引き戻し、同じ制限 Yoneda の実 shift 同型を使う。
規約：ラベルの単射性や選択集合への厳密な所属を要求しない。
使われ方：提示模型へ D-8 b の表現可能演算による一般判定を接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (I : Type w) [Small.{u} I] (value : I → RightModule R D)

def dgModuleFamilyYoneda :
    letI := inducedDGCategory R value
    DGFunctor R (RightModule R D) (RightModule R I) := by
  letI := inducedDGCategory R value
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorRestrictedYoneda R I (RightModule R D) (inducedDGEvaluation R value)

lemma dgModuleFamilyYoneda_obj (i : I) :
    letI := inducedDGCategory R value
    (dgModuleFamilyYoneda R D I value).obj (value i) = representable R i := by
  letI := inducedDGCategory R value
  apply EnrichedFunctor.ext (Complex R)
    (F := ((dgModuleFamilyYoneda R D I value).obj (value i)).toFunctor)
    (G := (representable R i).toFunctor) (fun _ => rfl)
  intro x y
  change (𝟙 _ ≫ (representable R (value i)).map
      (Opposite.op (value x.unop)) (Opposite.op (value y.unop))) ≫ eqToHom (by rfl) =
    (representable R i).map x y
  simp only [Category.id_comp, eqToHom_refl, Category.comp_id]
  rfl

def dgModuleFamilyShiftIso (i j : I) (s : ℤ)
    (e : (ForgetEnrichment.of (Complex R) (value i))⟦s⟧ ≅
      ForgetEnrichment.of (Complex R) (value j)) :
    letI := inducedDGCategory R value
    ForgetEnrichment.of (Complex R) (shiftModule s (representable R i)) ≅
      ForgetEnrichment.of (Complex R) (representable R j) := by
  letI := inducedDGCategory R value
  let F := dgModuleFamilyYoneda R D I value
  exact (eqToIso (congrArg
    (fun K => ForgetEnrichment.of (Complex R) (shiftModule s K))
    (dgModuleFamilyYoneda_obj R D I value i))).symm ≪≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorShiftIso R D I F s (value i)).symm ≪≫ F.onClosed.mapIso e ≪≫
    eqToIso (congrArg (ForgetEnrichment.of (Complex R))
      (dgModuleFamilyYoneda_obj R D I value j))

lemma dgModuleFamilyRepresentables_containsZero (i : I)
    (hi : IsZero (ForgetEnrichment.of (Complex R) (value i))) :
    letI := inducedDGCategory R value
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty R I).ContainsZero := by
  letI := inducedDGCategory R value
  have hz : IsZero (ForgetEnrichment.of (Complex R) (representable R i)) := by
    apply (module_isZero_iff R I _).2
    intro j
    exact moduleHom_isZero_tgt R D (value j) (value i)
      (fun x => (moduleEvaluation R D x).map_isZero hi)
  refine ⟨⟨(moduleToHomotopy R I).obj
    (ForgetEnrichment.of (Complex R) (representable R i)), ?_, ?_⟩⟩
  · exact (moduleToHomotopy R I).map_isZero hz
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_representable R I i

end SerrePositivity.InfinityCategories.Project.DerivedCategories
