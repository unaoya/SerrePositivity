module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# 基礎環から構造層の切断への作用

概要：A スキームの構造射から、各開の切断の A 代数構造を構成する。
方針：構造射の大域切断の写像を開へ制限する。
規約：スカラー作用は実際の環準同型で指定し、制限写像との両立を証明する。
使われ方：KST D4、Toën Derived Azumaya §3.2 の係数環層 H_X の構成。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.DerivedGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/--
概要：A スキームの構造射が誘導する大域切断への環準同型。
方針：Spec A の大域切断と A の標準同型を使う。
規約：構造射は明示的に与える。
使われ方：KST D4、Toën §3.2 の係数の基礎環の作用。
-/
def globalBaseMap (f : X ⟶ Spec (CommRingCat.of A)) : A →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

/--
概要：大域切断への環準同型を任意の開へ制限した写像。
方針：構造層の上限開からの制限写像と合成する。
規約：開ごとの平坦性を要求しない。
使われ方：KST D4、Toën §3.2 の H ⊗_A O_X(U) のスカラー作用。
-/
def sectionBaseMap (a : A →+* Γ(X, ⊤)) (U : X.Opens) : A →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp a

/--
概要：基礎環の作用は開集合の制限と両立する。
方針：構造層の前層としての合成則を使う。
規約：制限の向きは V から U。
使われ方：KST D4、Toën §3.2 の係数前層の制限写像。
-/
lemma restriction_comp_sectionBaseMap (a : A →+* Γ(X, ⊤))
    {U V : X.Opens} (i : U ⟶ V) :
    (X.presheaf.map i.op).hom.comp (sectionBaseMap a V) = sectionBaseMap a U := by
  ext r
  exact congrArg (fun g => g.hom (a r))
    (X.presheaf.map_comp (homOfLE (show V ≤ ⊤ from le_top)).op i.op).symm

/--
概要：構造層の切断の A 代数構造。
方針：制限した基礎環の写像から代数構造を作る。
規約：異なる構造射に由来する作用を暗黙の大域インスタンスにしない。
使われ方：KST D4、Toën §3.2 の係数テンソル積。
-/
@[instance_reducible]
def sectionAlgebra (a : A →+* Γ(X, ⊤)) (U : X.Opens) : Algebra A Γ(X, U) :=
  (sectionBaseMap a U).toAlgebra

/--
概要：構造層の制限を基礎環上の代数準同型として表す。
方針：制限と基礎環の作用の両立を用いる。
規約：代数構造を型の中で明示し、曖昧なスカラー作用を避ける。
使われ方：KST D4、Toën §3.2 の非可換係数テンソル前層。
-/
def sectionRestriction (a : A →+* Γ(X, ⊤)) {U V : X.Opens} (i : U ⟶ V) :
    letI := sectionAlgebra a V
    letI := sectionAlgebra a U
    Γ(X, V) →ₐ[A] Γ(X, U) := by
  letI := sectionAlgebra a V
  letI := sectionAlgebra a U
  exact
    { __ := (X.presheaf.map i.op).hom
      commutes' := fun r => congrArg (fun g : A →+* Γ(X, U) => g r)
        (restriction_comp_sectionBaseMap a i) }

end SerrePositivity.KST.DerivedGeometry
