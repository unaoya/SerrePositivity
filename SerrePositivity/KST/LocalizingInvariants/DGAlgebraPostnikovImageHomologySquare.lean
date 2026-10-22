module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerImageSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageHomology

/-!
概要：正方形に沿う実係数像のホモロジー射は、元のホモロジー正方形の像射になる。
方針：元の包含の単射性と shift 層の自然性を、像のホモロジー同型に沿って比較する。
規約：元の四辺と元の像包含を保持。使われ方：層の像同型を図式全体へ昇格する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C B' C' : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [B'.X.IsStrictlyLE 0] [C'.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (k : ℤ)
  (f : B ⟶ C) (f' : B' ⟶ C') (s : B ⟶ B') (t : C ⟶ C') (h : f ≫ t = s ≫ f')

def postnikovHomologySquare : Arrow.mk (homologyMap f.hom (-(n + 1))) ⟶
    Arrow.mk (homologyMap f'.hom (-(n + 1))) :=
  Arrow.homMk' (homologyMap s.hom (-(n + 1))) (homologyMap t.hom (-(n + 1))) (by
    rw [← homologyMap_comp, ← homologyMap_comp]
    have hc : f.hom ≫ t.hom = s.hom ≫ f'.hom := congrArg Mon.Hom.hom h
    exact congrArg (fun z => homologyMap z (-(n + 1))) hc.symm)

lemma postnikovShiftedLayerImageHomologyIso_square :
    homologyMap (postnikovShiftedLayerImageSquareMap R n hn k f f' s t h).hom (-(n + 1) - k) ≫
      (postnikovShiftedLayerImageHomologyIso R f' n hn k).hom =
        (postnikovShiftedLayerImageHomologyIso R f n hn k).hom ≫
          image.map (postnikovHomologySquare R n f f' s t h) := by
  let j : ℤ := -(n + 1) - k
  have hc : homologyMap (postnikovShiftedLayerImageSquareMap R n hn k f f' s t h).hom j ≫
      homologyMap (postnikovShiftedLayerImageInclusion R f' n hn k).hom j =
        homologyMap (postnikovShiftedLayerImageInclusion R f n hn k).hom j ≫
          homologyMap (postnikovShiftedLayerMap R C n hn k t).hom j := by
    rw [← homologyMap_comp, ← homologyMap_comp]
    exact congrArg (fun z => homologyMap z j)
      (postnikovShiftedLayerImageSquareMap_inclusion R n hn k f f' s t h)
  have hi : image.map (postnikovHomologySquare R n f f' s t h) ≫
      image.ι (homologyMap f'.hom (-(n + 1))) =
        image.ι (homologyMap f.hom (-(n + 1))) ≫ homologyMap t.hom (-(n + 1)) :=
    image.map_ι (postnikovHomologySquare R n f f' s t h)
  apply (cancel_mono (image.ι (homologyMap f'.hom (-(n + 1))))).1
  rw [Category.assoc, postnikovShiftedLayerImageHomologyIso_inclusion, ← Category.assoc, hc,
    Category.assoc, postnikovShiftedLayerHomologyIso_naturality, ← Category.assoc,
    ← postnikovShiftedLayerImageHomologyIso_inclusion]
  simpa only [Category.assoc] using (congrArg
    (fun z => (postnikovShiftedLayerImageHomologyIso R f n hn k).hom ≫ z) hi).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
