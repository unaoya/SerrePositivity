module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangePath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathPullbackDoubleLift

/-!
概要：底変更した平方零代数への二重経路の持ち上げと、経路の一意性を供給する。
方針：元の底変更 pullback 同型と二重経路 pullback を使う。
規約：元の底と class の全二重経路を保持。使われ方：共通底上の class coherence。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A B W : Mon (Complex R)} (q : A ⟶ B) (N : Bimod B B)

lemma baseChangePath_hom_ext
    {s t : W ⟶ DGAlgebra.Path.algebra R (algebra A (bimoduleRestrict q N))}
    (hp : s ≫ DGAlgebra.Path.map R (projection A (bimoduleRestrict q N)) =
      t ≫ DGAlgebra.Path.map R (projection A (bimoduleRestrict q N)))
    (hm : s ≫ DGAlgebra.Path.map R (baseChangeMap q N) =
      t ≫ DGAlgebra.Path.map R (baseChangeMap q N)) : s = t := by
  let e := (DGAlgebra.Path.functor R).mapIso (baseChangeIso q N)
  apply (cancel_mono e.hom).1
  apply Mon.Hom.ext
  apply DGAlgebra.PathPullback.chain_ext R q (projection B N)
  · change ((s ≫ DGAlgebra.Path.map R (baseChangeIso q N).hom) ≫
      DGAlgebra.Path.map R (MonoidPullback.fst _ _)).hom =
      ((t ≫ DGAlgebra.Path.map R (baseChangeIso q N).hom) ≫
        DGAlgebra.Path.map R (MonoidPullback.fst _ _)).hom
    simpa only [Category.assoc, ← DGAlgebra.Path.map_comp, baseChangeIso_projection,
      Mon.comp_hom'] using congrArg Mon.Hom.hom hp
  · change ((s ≫ DGAlgebra.Path.map R (baseChangeIso q N).hom) ≫
      DGAlgebra.Path.map R (MonoidPullback.snd _ _)).hom =
      ((t ≫ DGAlgebra.Path.map R (baseChangeIso q N).hom) ≫
        DGAlgebra.Path.map R (MonoidPullback.snd _ _)).hom
    simpa only [Category.assoc, ← DGAlgebra.Path.map_comp, baseChangeIso_map,
      Mon.comp_hom'] using congrArg Mon.Hom.hom hm

variable (a : W ⟶ DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R A))
  (b : W ⟶ DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (algebra B N)))
  (h : a ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R q) =
    b ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)))

def baseChangeDoublePathLift : W ⟶ DGAlgebra.Path.algebra R
    (DGAlgebra.Path.algebra R (algebra A (bimoduleRestrict q N))) :=
  DGAlgebra.PathPullback.doubleLift R q (projection B N) a b h ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (baseChangeIso q N).inv)

lemma baseChangeDoublePathLift_projection : baseChangeDoublePathLift q N a b h ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection A (bimoduleRestrict q N))) = a := by
  rw [baseChangeDoublePathLift, Category.assoc, ← DGAlgebra.Path.map_comp,
    ← DGAlgebra.Path.map_comp, baseChangeIso_inv_projection, DGAlgebra.PathPullback.doubleLift_fst]

lemma baseChangeDoublePathLift_map : baseChangeDoublePathLift q N a b h ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (baseChangeMap q N)) = b := by
  rw [baseChangeDoublePathLift, Category.assoc, ← DGAlgebra.Path.map_comp,
    ← DGAlgebra.Path.map_comp, baseChangeIso_inv_map, DGAlgebra.PathPullback.doubleLift_snd]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
