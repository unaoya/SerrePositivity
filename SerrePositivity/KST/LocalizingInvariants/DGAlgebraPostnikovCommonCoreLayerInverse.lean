module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreZeroInverse

/-!
概要：任意の切断次数の共通零底逆を、元の roof 底上の層逆へ戻す。
方針：同じ零底係数を共通核の制限比較へ渡し、元の両三角形を保持する。
規約：逆や細分を選び直さない。使われ方：Common の class・W 構成の一般化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m}
  (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

structure LayerInverse where
  zero : ZeroInverse R hn f c
  coefficient : denominatorLayer R hn f (c.refine R zero.source_le) ⟶
    numeratorLayer R hn f (c.refine R zero.source_le)
  coefficient_hom : coefficient.hom = zero.coefficient.hom
  left_coefficient : postnikovLayerMap R (f.app zero.stage).hom n ≫ coefficient.hom =
    postnikovLayerMap R (A.transition (zero.inverse_le.trans zero.stage_le)).hom n
  right_coefficient : coefficient.hom ≫ postnikovLayerMap R (f.app i).hom n =
    postnikovLayerMap R (B.transition (zero.inverse_le.trans zero.stage_le)).hom n

namespace LayerInverse

def ofZeroInverse (d : ZeroInverse R hn f c) : LayerInverse R hn f c where
  zero := d
  coefficient := coefficientFromZero R hn f (c.refine R d.source_le) d.coefficient
  coefficient_hom := coefficientFromZero_hom R hn f (c.refine R d.source_le) d.coefficient
  left_coefficient :=
    (congrArg (fun t => postnikovLayerMap R (f.app d.stage).hom n ≫ t)
      (coefficientFromZero_hom R hn f (c.refine R d.source_le) d.coefficient)).trans
        d.left_coefficient
  right_coefficient :=
    (congrArg (fun t => t ≫ postnikovLayerMap R (f.app i).hom n)
      (coefficientFromZero_hom R hn f (c.refine R d.source_le) d.coefficient)).trans
        d.right_coefficient

def ofInput (d : Input R hn f c) : LayerInverse R hn f c :=
  ofZeroInverse R hn f c (ZeroInverse.ofInput R hn f c d)

lemma exists_after
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (hₙ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R (n + 1)))) (bound : ℕ) :
    ∃ d : LayerInverse R hn f c, bound ≤ d.zero.stage := by
  obtain ⟨d, hd⟩ := exists_input_after R hn f c h₀ hₙ bound
  exact ⟨ofInput R hn f c d, hd⟩

end LayerInverse
end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
