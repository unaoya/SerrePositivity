module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellOverClassComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPerturbedMapLaws
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovShiftedLayerSquare

/-!
概要：二つの実 dg 代数射に沿う Postnikov cell 自然性を、同じ端点の三経路にそろえる。
方針：摂動射の厳密な関手則で、直接経路と第一射・第二射の自然性経路を照合する。
規約：元の指定自然性経路を使う。使われ方：Γ の右側の自然性合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B C D P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (f : B ⟶ C) (g : C ⟶ D)

def postnikovCellLiftCompositionSource : cellResolution R (cellResolution R P) ⟶
    postnikovPerturbedExtension R D n hn :=
  (cellAugmentation R (cellResolution R P) ≫
    postnikovCellLiftOverSource R B C P n hn b f) ≫ postnikovPerturbedMap R g n hn

def postnikovCellLiftCompositionMiddle : cellResolution R (cellResolution R P) ⟶
    postnikovPerturbedExtension R D n hn :=
  cellAugmentation R (cellResolution R P) ≫
    postnikovCellLiftOverSource R C D P n hn (b ≫ postnikovMap R f n) g

def postnikovCellLiftCompositionTarget : cellResolution R (cellResolution R P) ⟶
    postnikovPerturbedExtension R D n hn :=
  cellAugmentation R (cellResolution R P) ≫
    postnikovCellLiftOverTarget R C D P n hn (b ≫ postnikovMap R f n) g

def postnikovCellLiftCompositionFirst : Path.Witness R
    (postnikovCellLiftCompositionSource R B C D P n hn b f g)
    (postnikovCellLiftCompositionMiddle R B C D P n hn b f g) := by
  let z := (postnikovCellLiftOverNaturalityWitness R B C P n hn b f).postcomp
    (postnikovPerturbedMap R g n hn)
  refine ⟨z.hom, z.source_eq, ?_⟩
  simpa only [postnikovCellLiftCompositionMiddle, postnikovCellLiftOverSource,
    postnikovCellLiftOverTarget, Category.assoc] using z.target_eq

def postnikovCellLiftCompositionSecond : Path.Witness R
    (postnikovCellLiftCompositionMiddle R B C D P n hn b f g)
    (postnikovCellLiftCompositionTarget R B C D P n hn b f g) :=
  postnikovCellLiftOverNaturalityWitness R C D P n hn (b ≫ postnikovMap R f n) g

def postnikovCellLiftCompositionDirect : Path.Witness R
    (postnikovCellLiftCompositionSource R B C D P n hn b f g)
    (postnikovCellLiftCompositionTarget R B C D P n hn b f g) := by
  let z := postnikovCellLiftOverNaturalityWitness R B D P n hn b (f ≫ g)
  refine ⟨z.hom, ?_, ?_⟩
  · simpa only [postnikovCellLiftCompositionSource, postnikovCellLiftOverSource,
      postnikovPerturbedMap_comp, Category.assoc] using z.source_eq
  · simpa only [postnikovCellLiftCompositionTarget, postnikovCellLiftOverTarget,
      postnikovMap_composition, Category.assoc] using z.target_eq

lemma postnikovCellLiftCompositionFirst_relative :
    (postnikovCellLiftCompositionFirst R B C D P n hn b f g).hom ≫
      Path.map R (postnikovPerturbedProjection R D n hn) =
    (postnikovCellLiftCompositionSource R B C D P n hn b f g ≫
      postnikovPerturbedProjection R D n hn) ≫ Path.diagonal R (postnikov R D n) := by
  change ((postnikovCellLiftOverNaturalityWitness R B C P n hn b f).hom ≫
    Path.map R (postnikovPerturbedMap R g n hn)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovPerturbedProjection_naturality,
    Path.map_comp, ← Category.assoc, postnikovCellOverNaturality_relative,
    Category.assoc, Path.diagonal_naturality]
  simp only [postnikovCellLiftCompositionSource, Category.assoc,
    postnikovPerturbedProjection_naturality]
  rw [← Category.assoc (postnikovPerturbedMap R f n hn),
    postnikovPerturbedProjection_naturality]
  simp only [Category.assoc]

lemma postnikovCellLiftCompositionSecond_relative :
    (postnikovCellLiftCompositionSecond R B C D P n hn b f g).hom ≫
      Path.map R (postnikovPerturbedProjection R D n hn) =
    (postnikovCellLiftCompositionMiddle R B C D P n hn b f g ≫
      postnikovPerturbedProjection R D n hn) ≫ Path.diagonal R (postnikov R D n) :=
  postnikovCellOverNaturality_relative R C D P n hn (b ≫ postnikovMap R f n) g

lemma postnikovCellLiftCompositionDirect_relative :
    (postnikovCellLiftCompositionDirect R B C D P n hn b f g).hom ≫
      Path.map R (postnikovPerturbedProjection R D n hn) =
    (postnikovCellLiftCompositionSource R B C D P n hn b f g ≫
      postnikovPerturbedProjection R D n hn) ≫ Path.diagonal R (postnikov R D n) := by
  have hz := postnikovCellOverNaturality_relative R B D P n hn b (f ≫ g)
  simpa only [postnikovCellLiftCompositionDirect, postnikovCellLiftCompositionSource,
    postnikovCellLiftOverSource, postnikovPerturbedMap_comp, Category.assoc] using hz

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
