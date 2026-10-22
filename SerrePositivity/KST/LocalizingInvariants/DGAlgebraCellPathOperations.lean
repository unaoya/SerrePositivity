module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraComposedPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeCellPathLift

/-!
概要：実乗法的経路の向き反転と合成を、明示した cell augmentation の後で構成する。
方針：経路代数の始点評価の全射準同型性で相対経路を作り、終点へ後合成する。
規約：元の源上の厳密な反転・合成を主張しない。使われ方：実 roof の共通細分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} {f g h : A ⟶ B}

/-- 元の乗法的経路を、元の cell augmentation の前合成後に向き反転する。 -/
def Witness.cellReverse (w : Witness R f g) :
    Witness R (cellAugmentation R A ≫ g) (cellAugmentation R A ≫ f) := by
  have he : w.hom ≫ source R B = (f ≫ diagonal R B) ≫ source R B := by
    rw [Category.assoc, diagonal_source, Category.comp_id]
    exact w.source_eq
  let v := (RelativePath.cellPathWitness R (source R B) (source_surjective R B)
    (source_quasiIso R B) w.hom (f ≫ diagonal R B) he).postcomp (target R B)
  exact { hom := v.hom
          source_eq := by simpa only [Category.assoc, w.target_eq] using v.source_eq
          target_eq := by
            simpa only [Category.assoc, diagonal_target, Category.comp_id] using v.target_eq }

/-- 接続可能な元の二経路を、同じ元の cell augmentation の後で一本にする。 -/
def Witness.cellComp (a : Witness R f g) (b : Witness R g h) :
    Witness R (cellAugmentation R A ≫ f) (cellAugmentation R A ≫ h) := by
  have he : (f ≫ ComposedPath.diagonal R B) ≫ ComposedPath.source R B =
      ComposedPath.lift R a b ≫ ComposedPath.source R B := by
    rw [Category.assoc, ComposedPath.diagonal_source, Category.comp_id,
      ComposedPath.lift_source]
  let v := (RelativePath.cellPathWitness R (ComposedPath.source R B)
    (ComposedPath.source_surjective R B) (ComposedPath.source_quasiIso R B)
    (f ≫ ComposedPath.diagonal R B) (ComposedPath.lift R a b) he).postcomp
      (ComposedPath.target R B)
  exact { hom := v.hom
          source_eq := by
            simpa only [Category.assoc, ComposedPath.diagonal_target, Category.comp_id]
              using v.source_eq
          target_eq := by
            simpa only [Category.assoc, ComposedPath.lift_target] using v.target_eq }

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
