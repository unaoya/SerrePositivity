module
public import SerrePositivity.DifferentialGraded.Module.RestrictionRepresentable
public import SerrePositivity.DifferentialGraded.Module.TensorSource
public import SerrePositivity.DifferentialGraded.Module.TensorAdjunction
public import SerrePositivity.DifferentialGraded.Functor.Components
/-!
概要：自由加群から制限した自由加群への、元の dg 関手の Hom 作用による閉射を構成する。
方針：代表加群の制限比較を左 tensor し、同じ成分を実閉射に束ねる。
規約：各成分を恒等 tensor と元の Hom 鎖写像に厳密に固定する。
使われ方：c′ の自由加群延長比較を閉射の全 Hom 係数と照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E)

def freeRestrictionComparison (y : D) (K : Complex R) :
    (freeAt y).obj K ⟶ (moduleRestriction R D E F.op).obj ((freeAt (F.obj y)).obj K) :=
  moduleMorphismMk R D
    (M := freeModule y K)
    (N := restrictModule R D E F.op (freeModule (F.obj y) K))
    (fun x => 𝟙 K ⊗ₘ F.map x.unop y) (by
    intro x z
    have h := tensorModuleFamilyMap_naturality R D K
      (M := representable R y)
      (N := restrictModule R D E F.op (representable R (F.obj y)))
      (fun x => F.map x.unop y) (representableRestriction_naturality R D E F y) x z
    dsimp only [freeModule, restrictModule, tensorModule, RightModule.map, RightModule.obj, RightModule.toFunctor,
      DGFunctor.comp, EnrichedFunctor.comp] at h ⊢
    simpa only [Category.assoc] using h)

lemma freeRestrictionComparison_eval (y x : D) (K : Complex R) :
    (moduleEvaluation R D x).map (freeRestrictionComparison R D E F y K) = 𝟙 K ⊗ₘ F.map x y :=
  moduleMorphismMk_eval R D _ _ x

lemma freeRestrictionComparison_freeHomEquiv (y : D) (K : Complex R) :
    freeHomEquiv R D y K ((moduleRestriction R D E F.op).obj ((freeAt (F.obj y)).obj K))
      (freeRestrictionComparison R D E F y K) =
    freeHomEquiv R E (F.obj y) K ((freeAt (F.obj y)).obj K) (𝟙 _) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  have hD := freeHomEquiv_apply R D y K
    ((moduleRestriction R D E F.op).obj ((freeAt (F.obj y)).obj K))
    (freeRestrictionComparison R D E F y K) n t
  have hE := freeHomEquiv_apply R E (F.obj y) K ((freeAt (F.obj y)).obj K) (𝟙 _) n t
  refine hD.trans (Eq.trans ?_ hE.symm)
  change @Eq ((K ⊗ homObject R E (F.obj y) (F.obj y)).X n) _ _
  rw [freeRestrictionComparison_eval, CategoryTheory.Functor.map_id]
  have hT := tensorMap_apply (𝟙 K) (F.map y y) n 0 n (add_zero n) t (unitElement R y).val
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, F.map_unitElement R] at hT
  exact hT


end SerrePositivity.DifferentialGraded
