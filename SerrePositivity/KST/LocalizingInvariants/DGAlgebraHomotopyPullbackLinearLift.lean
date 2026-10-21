module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackLinearPath

/-!
概要：全パラメータ複体の二脚と比較 cochain から、模型の複体への射を構成する。
方針：二つの実 pullback を順に持ち上げ、三成分の共同単射性を証明する。
規約：指定 cochain の境界式を保持する。使われ方：mapping cocone との実同型。
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

def complexLift : K ⟶ (algebra R f g).X :=
  pullback.lift (complexReplacement R f g a b h hb) b
    (complexReplacement_target R f g a b h hb)

lemma complexLift_replacedProjection :
    complexLift R f g a b h hb ≫ (replacedProjection R f g).hom =
      complexReplacement R f g a b h hb := pullback.lift_fst _ _ _

lemma complexLift_right : complexLift R f g a b h hb ≫ (right R f g).hom = b :=
  pullback.lift_snd _ _ _

lemma complexLift_left : complexLift R f g a b h hb ≫ (left R f g).hom = a := by
  change complexLift R f g a b h hb ≫
    ((replacedProjection R f g).hom ≫ (MappingPath.projection R f).hom) = _
  rw [← Category.assoc, complexLift_replacedProjection, complexReplacement_projection]

lemma complexLift_path : complexLift R f g a b h hb ≫ (path R f g).hom =
    complexPath R f g a b h hb := by
  change complexLift R f g a b h hb ≫
    ((replacedProjection R f g).hom ≫ (MappingPath.inclusion R f).hom) = _
  rw [← Category.assoc, complexLift_replacedProjection, complexReplacement_inclusion]

lemma complexLift_primitive :
    (Cochain.ofHom (complexLift R f g a b h hb)).comp (primitive R f g) (zero_add (-1)) = h := by
  rw [primitive, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.ofHom_comp, complexLift_path, complexPath_primitive]

lemma complex_hom_ext {u v : K ⟶ (algebra R f g).X}
    (ha : u ≫ (left R f g).hom = v ≫ (left R f g).hom)
    (hb : u ≫ (right R f g).hom = v ≫ (right R f g).hom)
    (hp : (Cochain.ofHom u).comp (primitive R f g) (zero_add (-1)) =
      (Cochain.ofHom v).comp (primitive R f g) (zero_add (-1))) : u = v := by
  have hPath : u ≫ (path R f g).hom = v ≫ (path R f g).hom := by
    have hs : (path R f g).hom ≫ (Path.source R B).hom = (left R f g).hom ≫ f.hom :=
      congrArg Mon.Hom.hom (path_source R f g)
    have ht : (path R f g).hom ≫ (Path.target R B).hom = (right R f g).hom ≫ g.hom :=
      congrArg Mon.Hom.hom (path_target R f g)
    apply Path.chain_ext R B
    · simpa only [Category.assoc, hs] using congrArg (fun a => a ≫ f.hom) ha
    · simpa only [Category.assoc, ht] using congrArg (fun a => a ≫ g.hom) hb
    · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
        Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
      exact hp
  apply pullback.hom_ext
  · change u ≫ (replacedProjection R f g).hom = v ≫ (replacedProjection R f g).hom
    apply pullback.hom_ext
    · change (u ≫ (replacedProjection R f g).hom) ≫ (MappingPath.inclusion R f).hom =
        (v ≫ (replacedProjection R f g).hom) ≫ (MappingPath.inclusion R f).hom
      change u ≫ ((replacedProjection R f g).hom ≫ (MappingPath.inclusion R f).hom) =
        v ≫ ((replacedProjection R f g).hom ≫ (MappingPath.inclusion R f).hom) at hPath
      simpa only [Category.assoc] using hPath
    · change (u ≫ (replacedProjection R f g).hom) ≫ (MappingPath.projection R f).hom =
        (v ≫ (replacedProjection R f g).hom) ≫ (MappingPath.projection R f).hom
      change u ≫ ((replacedProjection R f g).hom ≫ (MappingPath.projection R f).hom) =
        v ≫ ((replacedProjection R f g).hom ≫ (MappingPath.projection R f).hom) at ha
      simpa only [Category.assoc] using ha
  · exact hb

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
