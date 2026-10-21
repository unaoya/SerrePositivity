module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackCocone

/-!
概要：任意の全パラメータ複体の二脚と比較 cochain を、模型の経路へ持ち上げる。
方針：実差の境界式から経路 cocone へ写し、mapping-path の複体 pullback を使う。
規約：代数射であることは要求しない。使われ方：模型の underlying 複体の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)} (f : A ⟶ B) (g : C ⟶ B)
  {K : Complex R} (a : K ⟶ A.X) (b : K ⟶ C.X) (h : Cochain K B.X (-1))
  (hb : δ (-1) 0 h + Cochain.ofHom (a ≫ f.hom - b ≫ g.hom) = 0)

include hb in
lemma complexPath_boundary : δ (-1) 0 h +
    Cochain.ofHom (biprod.lift (a ≫ f.hom) (b ≫ g.hom) ≫ Path.difference R B) = 0 := by
  rw [Path.difference_eq, Preadditive.comp_sub, biprod.lift_fst, biprod.lift_snd]
  exact hb

def complexPath : K ⟶ (Path.algebra R B).X :=
  mappingCocone.lift (Path.difference R B) (biprod.lift (a ≫ f.hom) (b ≫ g.hom)) h
    (complexPath_boundary R f g a b h hb)

lemma complexPath_endpoints : complexPath R f g a b h hb ≫ Path.endpointsHom R B =
    biprod.lift (a ≫ f.hom) (b ≫ g.hom) := mappingCocone.lift_fst _ _ _ _

lemma complexPath_source : complexPath R f g a b h hb ≫ (Path.source R B).hom = a ≫ f.hom := by
  change complexPath R f g a b h hb ≫ (Path.endpointsHom R B ≫ biprod.fst) = _
  rw [← Category.assoc, complexPath_endpoints, biprod.lift_fst]

lemma complexPath_target : complexPath R f g a b h hb ≫ (Path.target R B).hom = b ≫ g.hom := by
  change complexPath R f g a b h hb ≫ (Path.endpointsHom R B ≫ biprod.snd) = _
  rw [← Category.assoc, complexPath_endpoints, biprod.lift_snd]

lemma complexPath_primitive :
    (Cochain.ofHom (complexPath R f g a b h hb)).comp (Path.primitive R B) (zero_add (-1)) = h := by
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v _ _ _ _ p q hpq

def complexReplacement : K ⟶ (MappingPath.algebra R f).X :=
  pullback.lift (complexPath R f g a b h hb) a (complexPath_source R f g a b h hb)

lemma complexReplacement_inclusion :
    complexReplacement R f g a b h hb ≫ (MappingPath.inclusion R f).hom =
      complexPath R f g a b h hb := pullback.lift_fst _ _ _

lemma complexReplacement_projection :
    complexReplacement R f g a b h hb ≫ (MappingPath.projection R f).hom = a :=
  pullback.lift_snd _ _ _

lemma complexReplacement_target :
    complexReplacement R f g a b h hb ≫ (MappingPath.target R f).hom = b ≫ g.hom := by
  change complexReplacement R f g a b h hb ≫
    ((MappingPath.inclusion R f).hom ≫ (Path.target R B).hom) = _
  rw [← Category.assoc, complexReplacement_inclusion, complexPath_target]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
