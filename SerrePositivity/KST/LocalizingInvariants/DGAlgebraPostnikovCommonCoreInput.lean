module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCore
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovRoofLayerInverseData
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassEndpoints

/-!
概要：任意の切断次数の共通零底・層逆を Common 共通核の入力へ接続する。
方針：下段 roof の次数を推論し、同じ細分と係数の両三角形を保持する。
規約：shift は独立の整数引数。使われ方：class・W 構成と n=1 特殊化の共通入力。
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

abbrev Input := PostnikovRoofLayerInverseData R n hn f c

lemma exists_input_after
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (hₙ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R (n + 1)))) (bound : ℕ) :
    ∃ d : Input R hn f c, bound ≤ d.stage :=
  exists_postnikovRoofLayerInverseData_after R n hn f c h₀ hₙ bound

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

variable (d : Input R hn f c)

abbrev refinedRoof := c.refine R d.source_le

def coefficient : denominatorLayer R hn f (refinedRoof R hn f c d) ⟶
    numeratorLayer R hn f (refinedRoof R hn f c d) :=
  d.coefficient R n hn f c

lemma coefficient_left : postnikovLayerMap R (f.app d.stage).hom n ≫
    (coefficient R hn f c d).hom =
      postnikovLayerMap R (A.transition (d.target_le.trans d.inverse_le)).hom n :=
  d.coefficient_left R n hn f c

lemma coefficient_right : (coefficient R hn f c d).hom ≫
    postnikovLayerMap R (f.app i).hom n =
      postnikovLayerMap R (B.transition (d.target_le.trans d.inverse_le)).hom n :=
  d.coefficient_right R n hn f c

abbrev sourceClass :=
  classSource R hn f (refinedRoof R hn f c d) (coefficient R hn f c d)

abbrev targetClass := classTarget R hn f (refinedRoof R hn f c d)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
