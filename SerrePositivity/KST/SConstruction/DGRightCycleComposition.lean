module
public import SerrePositivity.DifferentialGraded.Category.Components
public import SerrePositivity.DifferentialGraded.Complexes.RightUnitorEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.MapEvaluation

/-! # 元の閉零射による dg Hom の右合成
概要：元の閉零射との右合成を、元の Hom 複体間の実鎖射として構成する。
方針：右単位の逆、閉零射からの単位鎖射、元の豊穣合成を合成する。
規約：元の豊穣順と次数を保持。使われ方：HA の右端一面制限と微分条件の帰納。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の閉零射との右合成は、元の Hom 複体間の実鎖射を与える。 -/
def dgRightCycleComposition {x y z : D} (g : zeroCycles (homObject A D y z)) :
    homObject A D x y ⟶ homObject A D x z :=
  (ρ_ (homObject A D x y)).inv ≫
    (𝟙 (homObject A D x y) ⊗ₘ unitFromCycle (homObject A D y z) g) ≫
      eComp (Complex A) x y z

/-- 元の閉零射との実鎖射は、任意の斉次元上で同じ豊穣順合成を回収する。 -/
lemma dgRightCycleComposition_apply {x y z : D} (g : zeroCycles (homObject A D y z))
    (k : ℤ) (f : GradedHom A x y k) :
    (dgRightCycleComposition A (x := x) g).f k f = forward A f g.val (add_zero k) := by
  have h (P Q : Complex A) (F : 𝟙_ (Complex A) ⟶ Q) (k : ℤ) (w : P.X k) :
      ((ρ_ P).inv ≫ (𝟙 P ⊗ₘ F)).f k w =
        ιTensorObj P Q k 0 k (add_zero k) (w ⊗ₜ[A] (cycleFromUnit Q F).val) := by
    rw [chain_comp_apply, complexRightUnitor_inv_apply, tensorMap_apply]
    rfl
  have ht := congrArg (fun w => (eComp (Complex A) x y z).f k w)
    (h (homObject A D x y) (homObject A D y z) (unitFromCycle _ g) k f)
  have he := congrArg Subtype.val (cycleFromUnit_unitFromCycle (homObject A D y z) g)
  exact ht.trans (congrArg (fun w => forward A f w (add_zero k)) he)

end SerrePositivity.KST.SConstruction
