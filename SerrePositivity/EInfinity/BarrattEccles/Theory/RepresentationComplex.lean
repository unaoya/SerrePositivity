module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorDegreeRepresentation
public import Mathlib.Algebra.Homology.Embedding.Restriction

/-!
# 群作用を持つ複体を表現の圏で読む

## 概要
HA 3.2.4.7 の二色比較のため、複体の自己射による群作用を表現の圏の複体へ持ち上げる。

## 方針
各次数に既存の表現を置き、作用射と微分の可換性から微分を表現の射にする。

## 規約
群作用は左作用。忘却すると元の全複体と射を保つ。

## 使われ方
二色の係数複体の射影解像度と、その指定された増大と比較射。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory HomologicalComplex
variable {A G : Type u} [CommRing A] [Group G]
  {K L : CochainComplex (ModuleCat.{u} A) ℤ}

/-- 複体の群作用を、表現の圏の複体にする。 -/
def representationCochainComplex (ρ : G →* End K) : CochainComplex (Rep.{u} A G) ℤ where
  X i := Rep.of (complexDegreeRepresentation ρ i)
  d i j := Rep.ofHom ⟨(K.d i j).hom, fun g =>
    congrArg ModuleCat.Hom.hom ((ρ g).asHom.comm i j)⟩
  shape i j h := by
    apply (forget₂ (Rep.{u} A G) (ModuleCat.{u} A)).map_injective
    exact K.shape i j h
  d_comp_d' i j k _ _ := by
    apply (forget₂ (Rep.{u} A G) (ModuleCat.{u} A)).map_injective
    exact K.d_comp_d i j k

/-- 表現への持ち上げの忘却は元の複体と同型であり、各成分は恒等射。 -/
def representationCochainForgetIso (ρ : G →* End K) :
    ((forget₂ (Rep.{u} A G) (ModuleCat.{u} A)).mapHomologicalComplex (.up ℤ)).obj
      (representationCochainComplex ρ) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j h
    simp
    rfl)

/-- 群作用と可換な複体射を、表現の圏の複体射へ持ち上げる。 -/
def representationCochainMap (ρ : G →* End K) (σ : G →* End L)
    (f : K ⟶ L) (hf : ∀ g, (ρ g).asHom ≫ f = f ≫ (σ g).asHom) :
    representationCochainComplex ρ ⟶ representationCochainComplex σ where
  f i := Rep.ofHom ⟨(f.f i).hom, fun g =>
    congrArg ModuleCat.Hom.hom (congrArg (fun h => h.f i) (hf g))⟩
  comm' i j _ := by
    apply (forget₂ (Rep.{u} A G) (ModuleCat.{u} A)).map_injective
    exact f.comm i j

/-- 同変射を持ち上げた後の各次数の忘却は、元の指定射そのものである。 -/
lemma representationCochainMap_forget_f (ρ : G →* End K) (σ : G →* End L)
    (f : K ⟶ L) (hf : ∀ g, (ρ g).asHom ≫ f = f ≫ (σ g).asHom) (i : ℤ) :
    (forget₂ (Rep.{u} A G) (ModuleCat.{u} A)).map
      ((representationCochainMap ρ σ f hf).f i) = f.f i := rfl

end SerrePositivity.EInfinity
