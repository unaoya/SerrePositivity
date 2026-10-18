module

public import SerrePositivity.KST.DerivedGeometry.BaseSections
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# 開部分上の基礎環の作用

概要：大域切断から指定した A 作用を開部分へ制限する。
方針：開部分の切断を開像上の切断として扱い、前層の合成則を使う。
規約：代数構造の等式と切断の型の一致を区別する。
使われ方：KST D4、Toën Derived Azumaya §3.2 の係数環層の制限。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.DerivedGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (a : A →+* Γ(X, ⊤))

/--
概要：開部分 U の大域切断への基礎環写像。
方針：U の全体の開像へ a を制限する。
規約：開像の全体を U と定義的に同一視しない。
使われ方：KST D4、Toën §3.2 の直接構成した局所係数環層。
-/
def restrictedBaseMap (U : X.Opens) : A →+* Γ(U, ⊤) :=
  sectionBaseMap a (U.ι ''ᵁ ⊤)

/--
概要：構造射を開部分へ制限して得る基礎環写像は大域切断の制限と一致する。
方針：合成の大域切断と開部分の包含の大域切断を展開する。
規約：制限した構造射は U.ι と元の構造射の合成。
使われ方：KST D4、Toën §3.2 の実際の係数環層の開制限。
-/
lemma globalBaseMap_restrict (f : X ⟶ Spec (CommRingCat.of A)) (U : X.Opens) :
    globalBaseMap (U.ι ≫ f) = restrictedBaseMap (globalBaseMap f) U := rfl

/--
概要：開部分内の切断の基礎環写像は、その開像への制限と一致する。
方針：二段の制限と一段の制限の一致を使う。
規約：環準同型の等式として作用を比較する。
使われ方：KST D4、Toën §3.2 の係数テンソルのスカラーの比較。
-/
lemma sectionBaseMap_restrict (U : X.Opens) (V : U.toScheme.Opens) :
    sectionBaseMap (restrictedBaseMap a U) V = sectionBaseMap a (U.ι ''ᵁ V) :=
  restriction_comp_sectionBaseMap a (U.ι.opensFunctor.map (homOfLE (show V ≤ ⊤ from le_top)))

/--
概要：開部分の切断への A 代数構造は開像の切断への A 代数構造と一致する。
方針：基礎環写像の等式から代数構造を同定する。
規約：この等式によってテンソル環のスカラー作用を移送する。
使われ方：KST D4、Toën §3.2 の係数前層の制限の比較。
-/
lemma sectionAlgebra_restrict (U : X.Opens) (V : U.toScheme.Opens) :
    sectionAlgebra (restrictedBaseMap a U) V = sectionAlgebra a (U.ι ''ᵁ V) := by
  exact congrArg RingHom.toAlgebra (sectionBaseMap_restrict a U V)

end SerrePositivity.KST.DerivedGeometry
