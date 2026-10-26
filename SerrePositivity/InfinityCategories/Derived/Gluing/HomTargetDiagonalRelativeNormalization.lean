module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCoefficientInputPathLegs
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetRelativeNormalization
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPathHomotopyPrism
/-!
概要：元終域の正規化 prism を、元入力付き係数対角の全区間族と両端固定で比較する。
方針：元 Hom 空間から区間 Hom への射で相対 homotopy を送る。
規約：同じ全 path を保つ。使われ方：指定対角境界の係数辺の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetNormalizedIntervalPrism :=
  dgGluingHomTargetNormalizedPrism R C D E p q X Y ≫
    pinchedHomToIntervalMappingSpace (X := dgNerve R E)
      (Simplex.vertex (p.obj X.left)) (Simplex.vertex (q.obj Y.right))

def dgGluingHomTargetCoefficientDiagonalPrism :=
  (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom ≫
    (dgGluingHomTargetCoefficientDiagonalHomotopy R C D E p q X Y).h

lemma dgGluingHomTargetCoefficientDiagonalPrism_eq :
    uncurry (dgGluingHomTargetCoefficientIntervalPath R C D E p q X Y) ≫
      pinchedHomToIntervalMappingSpace (X := dgNerve R E)
        (Simplex.vertex (p.obj X.left)) (Simplex.vertex (q.obj Y.right)) =
    dgGluingHomTargetCoefficientDiagonalPrism R C D E p q X Y := by
  change _ = (β_ (Δ[1] : SSet.{max (u + 1) v}) P).hom ≫
    (dgGluingIntervalPathHomotopy (dgGluingHomTargetCoefficientDiagonalPath R C D E p q X Y)).h
  rw [dgGluingIntervalPathHomotopy_prism, dgGluingHomTargetCoefficientDiagonalPath,
    dgGluingHomTargetCoefficientInputPathComparison_path, uncurry_natural_right]

lemma dgGluingHomTargetDiagonalRelativeNormalization_exists :
    ∃ H : SSet.Homotopy (dgGluingHomTargetNormalizedIntervalPrism R C D E p q X Y)
        (dgGluingHomTargetCoefficientDiagonalPrism R C D E p q X Y),
      (((SSet.boundary 1).ι ▷ P) ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max (u + 1) v}) ⊗ P) Δ[1] ≫
          ((SSet.boundary 1).ι ▷ P) ≫
            dgGluingHomTargetCoefficientDiagonalPrism R C D E p q X Y := by
  obtain ⟨H, hH⟩ := dgGluingHomTargetRelativeNormalization_exists R C D E p q X Y
  let t := pinchedHomToIntervalMappingSpace (X := dgNerve R E)
    (Simplex.vertex (p.obj X.left)) (Simplex.vertex (q.obj Y.right))
  let T := functorHomotopyPostcomp H t
  let U := stableHomotopyRetarget T rfl
    (dgGluingHomTargetCoefficientDiagonalPrism_eq R C D E p q X Y)
  refine ⟨U, ?_⟩
  have hU : U.h = H.h ≫ t := dgGluingHomotopyRetarget_h T _ _
  rw [hU, ← Category.assoc, hH, Category.assoc, Category.assoc,
    dgGluingHomTargetCoefficientDiagonalPrism_eq]

end SerrePositivity.InfinityCategories
