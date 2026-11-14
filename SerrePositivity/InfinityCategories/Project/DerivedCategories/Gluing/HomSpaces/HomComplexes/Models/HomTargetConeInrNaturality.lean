module
public import SerrePositivity.KST.SConstruction.DGHomGluingConeConnectingComparison
public import SerrePositivity.KST.SConstruction.DGHomGluingConeRightRestriction
/-!
概要：元の実 cone 右包含は、元 Hom gluing の全三成分 Hom 複体に関して自然である。
方針：三成分 end の評価と標準右包含への制限式を使い、全次数自然性を回収する。
規約：第三成分の零性は仮定しない。使われ方：実右軸上の cone 回収同型。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]

lemma dgGluingModuleConeElement_inr {M N P Q : ModuleCategory R E}
    (f : M ⟶ N) (g : P ⟶ Q) {n m : ℤ} (a) (b) (h) (hm : m + 1 = n) :
    (eHomWhiskerRight (Complex R) (moduleConeInr R E f) (moduleCone R E g)).f n
        (dgGluingModuleConeElement R E f g a b h hm) =
      (eHomWhiskerLeft (Complex R) N (moduleConeInr R E g)).f n b := by
  apply moduleHomElement_ext R E
    (M := ForgetEnrichment.to (Complex R) N)
    (N := ForgetEnrichment.to (Complex R) (moduleCone R E g))
  intro x
  apply (moduleHomWhiskerRight_apply_π R E (P := moduleCone R E g)
    (moduleConeInr R E f) n (dgGluingModuleConeElement R E f g a b h hm) x).trans
  apply Eq.trans _ (moduleHomWhiskerLeft_apply_π R E (T := N)
    (moduleConeInr R E g) n b x).symm
  rw [dgGluingModuleConeElement_π, moduleConeInr_eval, moduleConeInr_eval]
  exact dgGluingConeCochain_inr _ _ _ _ _ hm

attribute [local irreducible] dgHomGluingBimodule

variable (C : Type w) [DGCategory R C] [Small.{u} C]
  (D : Type z) [DGCategory R D] (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)

def dgGluingHomTargetRightYoneda : DGFunctor R G (RightModule R E) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D (dgHomGluingBimodule R C D E p q)).comp q).comp (dgYoneda R E)

lemma dgGluingHomTargetConeInr_naturality (X Y : G) :
    (dgGluingHomTargetRightYoneda R E C D p q).map X Y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) ((dgGluingHomTargetRightYoneda R E C D p q).obj X))
        (moduleConeInr R E (dgHomGluingTargetModuleMap R C D E p q Y)) =
    (dgHomGluingModuleConeFunctor R C D E p q).map X Y ≫
      eHomWhiskerRight (Complex R)
        (moduleConeInr R E (dgHomGluingTargetModuleMap R C D E p q X))
        (ForgetEnrichment.of (Complex R) ((dgHomGluingModuleConeFunctor R C D E p q).obj Y)) := by
  simp only [dgGluingHomTargetRightYoneda, DGFunctor.comp, EnrichedFunctor.comp_map]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight_map]
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (representable R (q.obj X.right)))
      (moduleConeInr R E (dgHomGluingTargetModuleMap R C D E p q Y))).f n
      ((dgHomGluingConeRightMap R C D E p q X Y).f n a) =
    (eHomWhiskerRight (Complex R)
      (moduleConeInr R E (dgHomGluingTargetModuleMap R C D E p q X))
      (moduleCone R E (dgHomGluingTargetModuleMap R C D E p q Y))).f n
      ((dgHomGluingConeHomMap R C D E p q X Y).f n a)
  exact (dgGluingModuleConeElement_inr R E
    (dgHomGluingTargetModuleMap R C D E p q X)
    (dgHomGluingTargetModuleMap R C D E p q Y)
    ((dgHomGluingConeLeftMap R C D E p q X Y).f n a)
    ((dgHomGluingConeRightMap R C D E p q X Y).f n a)
    ((dgHomGluingConePrimitive R C D E p q X Y).v n (n - 1) (by omega) a) (by omega)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
