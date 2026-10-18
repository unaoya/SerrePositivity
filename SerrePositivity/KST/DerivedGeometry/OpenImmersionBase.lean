module

public import SerrePositivity.KST.DerivedGeometry.BaseSections
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Modules.Presheaf

/-!
# 開埋め込みに沿う基礎環の作用

概要：開埋め込みの切断環の同型が基礎環の作用を保つことを示す。
方針：構造射の切断写像と appIso の逆の可換式を使う。
規約：X 上の作用は大域切断の引き戻しとして指定する。
使われ方：KST D4、Toën Derived Azumaya §3.2 のアフィン同型への輸送。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.DerivedGeometry

variable {A : Type u} [CommRing A] {X Y : Scheme.{u}}

/--
概要：開埋め込みの逆向きの切断同型を構造層の環前層射として束ねる。
方針：appIso の逆の自然性を使い、可換環から環へ忘れる。
規約：開像の関手への前合成を終域とする。
使われ方：KST D4、Toën §3.2 の開埋め込みに沿う係数構造。
-/
def openImmersionStructureMap (f : X ⟶ Y) [IsOpenImmersion f] :
    X.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ Y.ringCatSheaf.obj :=
  Functor.whiskerRight
    (show X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf from
      { app := fun V => (f.appIso V.unop).inv
        naturality := fun {_V _W} i => f.appIso_inv_naturality i })
    (forget₂ CommRingCat RingCat)

/--
概要：スキームの射に沿って基礎環の大域切断への写像を引き戻す。
方針：大域切断の反変写像を後合成する。
規約：射の平坦性を要求しない。
使われ方：KST D4、Toën §3.2 の局所係数構造。
-/
def pullbackBaseMap (a : A →+* Γ(Y, ⊤)) (f : X ⟶ Y) : A →+* Γ(X, ⊤) :=
  f.appTop.hom.comp a

/--
概要：開埋め込みの appIso の逆は切断の基礎環写像を保つ。
方針：全体からの appLE と appIso の逆の合成の式を使う。
規約：環準同型の等式として述べる。
使われ方：KST D4、Toën §3.2 の係数テンソルの A 線形な輸送。
-/
lemma appIso_inv_comp_sectionBaseMap (a : A →+* Γ(Y, ⊤)) (f : X ⟶ Y)
    [IsOpenImmersion f] (V : X.Opens) :
    (f.appIso V).inv.hom.comp (sectionBaseMap (pullbackBaseMap a f) V) =
      sectionBaseMap a (f ''ᵁ V) := by
  have h := f.appLE_appIso_inv (U := ⊤) (V := V) (by simp)
  exact congrArg (fun g : Γ(Y, ⊤) ⟶ Γ(Y, f ''ᵁ V) => g.hom.comp a) h

/--
概要：開埋め込みの切断環の同型の逆は A 代数の同型になる。
方針：appIso の環同型に基礎環の作用との両立を添える。
規約：始域と終域の代数構造を sectionAlgebra で指定する。
使われ方：KST D4、Toën §3.2 のアフィンの係数テンソルの輸送。
-/
def openImmersionSectionAlgEquiv (a : A →+* Γ(Y, ⊤)) (f : X ⟶ Y)
    [IsOpenImmersion f] (V : X.Opens) :
    letI := sectionAlgebra (pullbackBaseMap a f) V
    letI := sectionAlgebra a (f ''ᵁ V)
    Γ(X, V) ≃ₐ[A] Γ(Y, f ''ᵁ V) := by
  letI := sectionAlgebra (pullbackBaseMap a f) V
  letI := sectionAlgebra a (f ''ᵁ V)
  exact {
    toFun := (f.appIso V).inv
    invFun := (f.appIso V).hom
    left_inv := fun x => congrArg (fun g : Γ(X, V) ⟶ Γ(X, V) => g x)
      (f.appIso V).inv_hom_id
    right_inv := fun x => congrArg (fun g : Γ(Y, f ''ᵁ V) ⟶ Γ(Y, f ''ᵁ V) => g x)
      (f.appIso V).hom_inv_id
    map_mul' := map_mul _
    map_add' := map_add _
    commutes' := fun r => congrArg (fun g : A →+* Γ(Y, f ''ᵁ V) => g r)
      (appIso_inv_comp_sectionBaseMap a f V) }

end SerrePositivity.KST.DerivedGeometry
