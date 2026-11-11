module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoconePathModel

/-! 元の恒等 cocone と係数複体からなる、指定始終点を持つ同じ実 path 複体。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] (Q : Complex R)

abbrev dgGluingComplexPath := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpan (𝟙 Q)

def dgGluingComplexPathStart : dgGluingComplexPath Q ⟶ Q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanLeft (𝟙 Q)

def dgGluingComplexPathEnd : dgGluingComplexPath Q ⟶ Q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanRight (𝟙 Q)

def dgGluingComplexPathEndpoints : dgGluingComplexPath Q ⟶ Q ⊞ Q :=
  biprod.lift (dgGluingComplexPathStart Q) (dgGluingComplexPathEnd Q)

def dgGluingComplexPathConstant : Q ⟶ dgGluingComplexPath Q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanSection (𝟙 Q)

lemma dgGluingComplexPathConstant_start :
    dgGluingComplexPathConstant Q ≫ dgGluingComplexPathStart Q = 𝟙 Q := by
  simp [dgGluingComplexPathConstant, dgGluingComplexPathStart,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanSection, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanLeft]

lemma dgGluingComplexPathConstant_end :
    dgGluingComplexPathConstant Q ≫ dgGluingComplexPathEnd Q = 𝟙 Q :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanSection_right _

lemma dgGluingComplexPathStart_quasiIso : QuasiIso (dgGluingComplexPathStart Q) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanLeft_quasiIso _

lemma dgGluingComplexPathEnd_quasiIso : QuasiIso (dgGluingComplexPathEnd Q) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanRight_quasiIso _

lemma dgGluingComplexPath_difference :
    (biprod.snd : dgGluingComplexPath Q ⟶ mappingCocone (𝟙 Q)) ≫ mappingCocone.fst (𝟙 Q) =
      dgGluingComplexPathEnd Q - dgGluingComplexPathStart Q := by
  simp [dgGluingComplexPathEnd, dgGluingComplexPathStart,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanRight, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanLeft]

def dgGluingComplexPathPrimitive : Cochain (dgGluingComplexPath Q) Q (-1) :=
  (Cochain.ofHom (biprod.snd : dgGluingComplexPath Q ⟶ mappingCocone (𝟙 Q))).comp
    (mappingCocone.snd (𝟙 Q)) (zero_add (-1))

lemma dgGluingComplexPathPrimitive_boundary :
    δ (-1) 0 (dgGluingComplexPathPrimitive Q) +
      Cochain.ofHom (dgGluingComplexPathEnd Q - dgGluingComplexPathStart Q) = 0 := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePathLift_boundary
    (dgGluingComplexPathEnd Q - dgGluingComplexPathStart Q)
    biprod.snd (𝟙 _) (by rw [Category.id_comp, dgGluingComplexPath_difference])

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
