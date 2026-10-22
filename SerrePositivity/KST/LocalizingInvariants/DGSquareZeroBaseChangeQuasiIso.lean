module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroUnderlyingMaps
public import SerrePositivity.KST.LocalizingInvariants.CochainBiprodQuasiIso

/-!
概要：平方零係数を制限する底変更射は、底の準同型性を保つ。
方針：underlying 射の二成分は元の底射と係数の恒等射である。
規約：係数作用の同一視で準同型性を仮定しない。使われ方：共通底拡大と元の拡大の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A B : Mon (Complex R)} (q : A ⟶ B) (N : Bimod B B)

lemma baseChangeMap_quasiIso (hq : QuasiIso q.hom) : QuasiIso (baseChangeMap q N).hom := by
  change QuasiIso (biprod.map q.hom (𝟙 N.X))
  exact cochainBiprodMap_quasiIso _ _ hq (quasiIso_of_isIso _)

end SerrePositivity.KST.LocalizingInvariants.SquareZero
