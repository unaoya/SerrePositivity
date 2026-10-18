module

public import SerrePositivity.KST.DerivedBlowup.ExteriorComplexMap

/-!
概要：KST §3.1 の Koszul cochain 射の等式移送と合成。
方針：微分の等式は等式帰納法、生成元写像の合成は零延長の関手性を使う。
規約：基底環と生成元加群の宇宙は独立。
使われ方：座標規格化の等式を伴うチャート cocycle。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R : Type u} [CommRing R]
  {M N P : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- 概要：始域の微分の同定は Koszul cochain 射の等式移送になる。
方針：微分の等式を消去し、証明項の一意性を使う。
規約：KST §3.1。使われ方：座標 cocycle による始域の同定。 -/
theorem exteriorKoszulCochainMap_transport_source (f : M →ₗ[R] N)
    (d d' : M →ₗ[R] R) (dN : N →ₗ[R] R) (hd : d = d')
    (h : dN.comp f = d) (h' : dN.comp f = d') :
    exteriorKoszulCochainMap f d dN h =
      eqToHom (congrArg exteriorKoszulCochain hd) ≫ exteriorKoszulCochainMap f d' dN h' := by
  subst d'
  simp

/-- 概要：生成元の合成の同定は Koszul cochain 射の合成の同定になる。
方針：生成元写像の等式を消去し、chain map の合成則を零延長する。
規約：KST §3.1。使われ方：異なる生成元加群のチャート cocycle。 -/
theorem exteriorKoszulCochainMap_comp_eq (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (k : M →ₗ[R] P) (dM : M →ₗ[R] R) (dN : N →ₗ[R] R) (dP : P →ₗ[R] R)
    (hf : dN.comp f = dM) (hg : dP.comp g = dN)
    (hk : dP.comp k = dM) (hfg : g.comp f = k) :
    exteriorKoszulCochainMap f dM dN hf ≫ exteriorKoszulCochainMap g dN dP hg =
      exteriorKoszulCochainMap k dM dP hk := by
  subst k
  dsimp only [exteriorKoszulCochainMap]
  rw [← HomologicalComplex.extendMap_comp, exteriorKoszulChainMap_comp f g dM dN dP hf hg hk]

end SerrePositivity.KST.DerivedBlowup
