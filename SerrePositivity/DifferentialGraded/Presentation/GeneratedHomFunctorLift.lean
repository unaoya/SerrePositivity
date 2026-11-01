module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomCategory
public import SerrePositivity.DifferentialGraded.Category.ObjectImage
/-!
概要：全 Hom 像が指定係数 span に入る dg 関手を、同じ実 dg 係数閉包へ持ち上げる。
方針：Hom 鎖写像を span へ制限し、忠実な評価で単位・合成を反映する。
規約：元の対象写像と全 Hom 作用を厳密に保持する。
使われ方：c′ の共通係数閉包に元の出発 dg 関手を収容する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SerrePositivity.InfinityCategories
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)
  (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
namespace DGGeneratedHomWord
variable (C : Type w) [DGCategory R C]
  (F : DGFunctor R C (DGObjectImage value))
  (hF : ∀ x y n (f : GradedHom R x y n), (F.map x y).f n f ∈
    linearSpan source target degree R D value coefficient ((F.obj x).label) ((F.obj y).label) n)

def liftHom (x y : C) : homObject R C x y ⟶
    homComplex source target degree R D value coefficient ((F.obj x).label) ((F.obj y).label) where
  f n := ModuleCat.ofHom (((F.map x y).f n).hom.codRestrict
    (linearSpan source target degree R D value coefficient ((F.obj x).label) ((F.obj y).label) n) (hF x y n))
  comm' n m hnm := by
    have hm : n + 1 = m := hnm
    subst m
    dsimp only [homComplex]
    rw [CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact congrArg (fun k => k f) ((F.map x y).comm n (n + 1))

lemma liftHom_inclusion (x y : C) :
    liftHom source target degree R D value coefficient C F hF x y ≫
      inclusion source target degree R D value coefficient ((F.obj x).label) ((F.obj y).label) = F.map x y := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

def liftFunctor :
    letI := category source target degree R D value coefficient
    DGFunctor R C J := by
  letI := category source target degree R D value coefficient
  exact
    { obj := fun x => (F.obj x).label
      map := liftHom source target degree R D value coefficient C F hF
      map_id x := by
        apply (cancel_mono (inclusion source target degree R D value coefficient ((F.obj x).label) ((F.obj x).label))).1
        change (eId (Complex R) x ≫ liftHom source target degree R D value coefficient C F hF x x) ≫
          inclusion source target degree R D value coefficient ((F.obj x).label) ((F.obj x).label) =
          homUnit source target degree R D value coefficient ((F.obj x).label) ≫
            inclusion source target degree R D value coefficient ((F.obj x).label) ((F.obj x).label)
        rw [Category.assoc, liftHom_inclusion, homUnit_inclusion]
        exact F.map_id x
      map_comp x y z := by
        apply (cancel_mono (inclusion source target degree R D value coefficient ((F.obj x).label) ((F.obj z).label))).1
        change (eComp (Complex R) x y z ≫
          liftHom source target degree R D value coefficient C F hF x z) ≫
          inclusion source target degree R D value coefficient ((F.obj x).label) ((F.obj z).label) =
          (liftHom source target degree R D value coefficient C F hF x y ⊗ₘ
            liftHom source target degree R D value coefficient C F hF y z) ≫
            homComposition source target degree R D value coefficient ((F.obj x).label) ((F.obj y).label) ((F.obj z).label) ≫
              inclusion source target degree R D value coefficient ((F.obj x).label) ((F.obj z).label)
        simp only [Category.assoc, liftHom_inclusion, homComposition_inclusion]
        rw [tensorHom_comp_tensorHom_assoc, liftHom_inclusion, liftHom_inclusion]
        exact F.map_comp x y z }

lemma liftFunctor_comp_evaluation :
    letI := category source target degree R D value coefficient
    (liftFunctor source target degree R D value coefficient C F hF).comp
      (evaluation source target degree R D value coefficient) = F.comp (dgObjectImageEvaluation R value) := by
  letI := category source target degree R D value coefficient
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, eqToHom_refl, Category.comp_id]

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
