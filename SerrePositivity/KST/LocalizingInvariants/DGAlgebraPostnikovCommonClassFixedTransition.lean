module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightFixedClassGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassAffine

/-!
概要：指定右経路の貼合せから、元の係数逆と標準 class に沿う新 class 互換性を作る。
方針：既存の後続段の係数逆と底変更同型を使い、標準 class 経路と同じ源上で合成する。
規約：元の両端・係数・共通底を保持。使われ方：整合する Γ 模型射の再構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} {hj : j ≤ i}
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

def postnikovCommonClassFixedRetractWitness : Path.Witness R
    (postnikovCommonClassRetractTarget R f c d (hj := hj))
    (postnikovCommonClassRetractSource R f c d (hj := hj)) where
  hom := (postnikovCommonRightFixedClassGlueWitness R f c d).hom ≫
    Path.map R (postnikovCommonRightRetract R f c d e)
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc,
      (postnikovCommonRightFixedClassGlueWitness R f c d).source_eq,
      postnikovCommonRightGlueTarget_retract]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc,
      (postnikovCommonRightFixedClassGlueWitness R f c d).target_eq,
      postnikovCommonRightGlueSource_retract]

lemma postnikovCommonClassFixedRetractWitness_projection :
    (postnikovCommonClassFixedRetractWitness R f c d e).hom ≫
      Path.map R (SquareZero.projection _ _) =
    postnikovCommonRightZeroGlueProjection R f c d ≫
      (postnikovCommonRightZeroBase R f c d ≫ e.base) ≫
        Path.diagonal R (postnikov R (A.obj j).obj 0) := by
  change (_ ≫ Path.map R (postnikovCommonRightRetract R f c d e)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonRightRetract_projection,
    Path.map_comp, ← Category.assoc, postnikovCommonRightFixedClassGlueWitness_projection,
    Category.assoc, Path.diagonal_naturality]

def postnikovCommonClassFixedRetractRelativeWitness : Path.Witness R
    (postnikovCommonClassRetractLeft R f c d e) (postnikovCommonClassRetractRight R f c d e) :=
  SquareZero.baseChangeWitness _ _ _ _ _ _ _ (postnikovCommonClassFixedRetractWitness R f c d e)
    (by
      rw [postnikovCommonClassFixedRetractWitness_projection,
        postnikovCommonClassRetractBase_zero R f c d e]
      simp only [Category.assoc])

lemma postnikovCommonClassFixedRetractRelativeWitness_projection :
    (postnikovCommonClassFixedRetractRelativeWitness R f c d e).hom ≫
      Path.map R (SquareZero.projection _ _) = postnikovCommonRightZeroGlueProjection R f c d ≫
        Path.diagonal R (postnikovCommonClassBase R f c d) :=
  SquareZero.baseChangeWitness_relative _ _ _ _ _ _ _ _ _

def postnikovCommonClassFixedTransitionWitness : Path.Witness R
    (postnikovCommonClassTransitionTarget R f c d (hj := hj))
    (postnikovCommonClassTransitionSource R f c d (hj := hj)) where
  hom := (postnikovCommonClassFixedRetractRelativeWitness R f c d e).hom ≫
    Path.map R (postnikovCommonClassTransitionIso R f c d hj).inv
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc,
      (postnikovCommonClassFixedRetractRelativeWitness R f c d e).source_eq,
      postnikovCommonClassRetractLeft_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc,
      (postnikovCommonClassFixedRetractRelativeWitness R f c d e).target_eq,
      postnikovCommonClassRetractRight_eq, Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma postnikovCommonClassFixedTransitionWitness_projection :
    (postnikovCommonClassFixedTransitionWitness R f c d e).hom ≫
      Path.map R (SquareZero.projection _ _) = postnikovCommonRightZeroGlueProjection R f c d ≫
        Path.diagonal R (postnikovCommonClassBase R f c d) := by
  change (_ ≫ Path.map R (postnikovCommonClassTransitionIso R f c d hj).inv) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, postnikovCommonClassTransitionIso,
    postnikovClassBaseZeroIso_inv_projection,
    postnikovCommonClassFixedRetractRelativeWitness_projection]

def postnikovCommonClassFixedTransitionRelative : SquareZero.RelativeWitness
    (postnikovCommonRightZeroGlueProjection R f c d)
    (postnikovCommonClassTransitionLayer R f c d hj)
    (postnikovCommonClassTransitionTarget R f c d (hj := hj))
    (postnikovCommonClassTransitionSource R f c d (hj := hj)) where
  toWitness := postnikovCommonClassFixedTransitionWitness R f c d e
  projection_eq := postnikovCommonClassFixedTransitionWitness_projection R f c d e

def postnikovCommonClassFixedCompatibility : SquareZero.RelativeWitness
    (postnikovCommonRightZeroGlueProjection R f c d)
    (postnikovCommonClassTransitionLayer R f c d hj)
    (postnikovCommonClassTransitionSource R f c d (hj := hj))
    (postnikovCommonClassStandardEndpoint R f c d hj) :=
  (postnikovCommonClassFixedTransitionRelative R f c d e).reverse.comp
    (postnikovCommonClassStandardRelative R f c d (hj := hj))

def postnikovCommonClassFixedGlueCompatibility : SquareZero.RelativeWitness
    (postnikovCommonClassStandardGlueProjection R f c d)
    (postnikovCommonClassTransitionLayer R f c d hj)
    (postnikovCommonClassStandardGlueLeft R f c d (hj := hj))
    (postnikovCommonClassStandardGlueRight R f c d (hj := hj)) :=
  (postnikovCommonClassFixedCompatibility R f c d e).precomp
    (cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R f c d))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
