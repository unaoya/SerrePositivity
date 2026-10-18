module

public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientTildeExact

/-!
概要：アフィン係数層の零対象の基礎構造層加群は準連接。
方針：零加群の実際の tilde と同型にし、既証の準連接性を移す。
規約：非可換・非平坦な係数を許す。
使われ方：TT §3・§8、Toën §3.2 のアフィン Dqc の切断での閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits ZeroObject AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]

/--
概要：零の係数加群層を忘却すると準連接。
方針：完全 tilde と忘却の加法性から零加群の像も零であることを使う。
規約：実際の全係数層の対象の零性から示す。
使われ方：TT §3、Toën §3.2 のコホモロジーが零となる切断の次数。
-/
lemma affineCoefficient_isQuasicoherent_of_isZero
    (M : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules) (hM : IsZero M) :
    ((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget.obj M).IsQuasicoherent := by
  let B := tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom
  let F₀ := (affineCoefficientEquivalence (R := R) H).inverse.obj (0 : ModuleCat.{u} H)
  have hz : IsZero (B.forget.obj F₀.obj) :=
    Functor.map_isZero (affineCoefficientTildeFunctor (R := R) H ⋙ B.forget) (isZero_zero _)
  exact (SheafOfModules.isQuasicoherent (Scheme.Spec.obj (.op R)).ringCatSheaf).prop_of_iso
    (hz.iso (Functor.map_isZero B.forget hM)) F₀.property

end SerrePositivity.KST.DerivedGeometry
