module

public import SerrePositivity.KST.DerivedGeometry.AffineSourceQcohHom

/-!
概要：全係数加群層へのアフィン tilde と H 大域切断の実際の随伴。
方針：準連接な始域から任意の終域への Hom 表示を係数同値の単位で移す。
規約：終域の準連接性も H の平坦性も要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数アフィン導来比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra R H]

/--
概要：全係数加群層への tilde の Hom は元の H 加群から大域切断への Hom と同値。
方針：準連接始域の Hom 表示とアフィン係数同値の単位を合成する。
規約：順写像は大域切断への写像と単位の合成。
使われ方：TT §3、Toën §3.2 の実際のアフィン随伴。
-/
def affineCoefficientTildeHomEquiv (M : ModuleCat.{u} H)
    (N : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules) :
    ((affineCoefficientTildeFunctor H).obj M ⟶ N) ≃ (M ⟶ (affineCoefficientΓ H).obj N) :=
  (affineCoefficientHomEquiv_of_sourceQC H ((affineCoefficientEquivalence (R := R) H).inverse.obj M) N).trans
    { toFun := fun f => ((affineCoefficientEquivalence (R := R) H).counitIso.symm.app M).hom ≫ f
      invFun := fun f => ((affineCoefficientEquivalence (R := R) H).counitIso.symm.app M).inv ≫ f
      left_inv f := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      right_inv f := by simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] }

/--
概要：tilde の Hom 同値は H 加群の射に関して反変に自然。
方針：係数大域切断の合成保存と係数同値の単位の自然性を使う。
規約：左側の射は元の全層への tilde 関手の像。
使われ方：TT §3、Toën §3.2 の随伴の構成。
-/
lemma affineCoefficientTildeHomEquiv_naturality_left {M M' : ModuleCat.{u} H}
    (f : M' ⟶ M)
    {N : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules}
    (g : (affineCoefficientTildeFunctor H).obj M ⟶ N) :
    affineCoefficientTildeHomEquiv H M' N ((affineCoefficientTildeFunctor H).map f ≫ g) =
      f ≫ affineCoefficientTildeHomEquiv H M N g := by
  change ((affineCoefficientEquivalence (R := R) H).counitIso.symm.app M').hom ≫
    (affineCoefficientΓ H).map ((affineCoefficientTildeFunctor H).map f ≫ g) =
      f ≫ ((affineCoefficientEquivalence (R := R) H).counitIso.symm.app M).hom ≫ (affineCoefficientΓ H).map g
  rw [Functor.map_comp, ← Category.assoc]
  have h := (affineCoefficientEquivalence (R := R) H).counitIso.symm.hom.naturality f
  change f ≫ ((affineCoefficientEquivalence (R := R) H).counitIso.symm.app M).hom =
    ((affineCoefficientEquivalence (R := R) H).counitIso.symm.app M').hom ≫
      (affineCoefficientΓ H).map ((affineCoefficientTildeFunctor H).map f) at h
  rw [← h, Category.assoc]

/--
概要：tilde の Hom 同値は全係数加群層の終域の射に関して自然。
方針：大域切断の関手の合成保存を使う。
規約：終域の準連接性を要求しない。
使われ方：TT §3、Toën §3.2 の全層への随伴。
-/
lemma affineCoefficientTildeHomEquiv_naturality_right (M : ModuleCat.{u} H)
    {N N' : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).Modules}
    (f : (affineCoefficientTildeFunctor H).obj M ⟶ N) (g : N ⟶ N') :
    affineCoefficientTildeHomEquiv H M N' (f ≫ g) =
      affineCoefficientTildeHomEquiv H M N f ≫ (affineCoefficientΓ H).map g := by
  change ((affineCoefficientEquivalence (R := R) H).counitIso.symm.app M).hom ≫
    (affineCoefficientΓ H).map (f ≫ g) =
      (((affineCoefficientEquivalence (R := R) H).counitIso.symm.app M).hom ≫ (affineCoefficientΓ H).map f) ≫
        (affineCoefficientΓ H).map g
  rw [Functor.map_comp, Category.assoc]

/--
概要：全係数加群層へのアフィン tilde は H 加群値の実際の大域切断の左随伴。
方針：証明した Hom 同値と両側の自然性から Mathlib の随伴を構成する。
規約：H の非可換性・非平坦性を許し、全係数加群層を右側の定義域とする。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数導来随伴。
-/
def affineCoefficientTildeAdjunction :
    affineCoefficientTildeFunctor (R := R) H ⊣ affineCoefficientΓ (R := R) H :=
  Adjunction.mkOfHomEquiv
    { homEquiv := affineCoefficientTildeHomEquiv H
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        apply (affineCoefficientTildeHomEquiv H M N).injective
        rw [Equiv.apply_symm_apply, affineCoefficientTildeHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun {M N N'} f g =>
        affineCoefficientTildeHomEquiv_naturality_right H M f g }

end SerrePositivity.KST.DerivedGeometry
