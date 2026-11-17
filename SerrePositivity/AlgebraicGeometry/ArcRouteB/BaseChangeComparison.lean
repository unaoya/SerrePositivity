module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.Definitions
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
概要：指定された係数の可換三角形について、二回と一回の底変換のArrowを同型にする。
方針：既存のtensor関手と押し出しの同型、押し出しの合成法則を使う。
規約：元の係数射を保ち、選ばれたČech余極限の内部を書き換えない。
使われ方：2iの照合法則L01、区間の制限と正次数の係数への移送。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 照合法則L01：同じ係数射の一回と二回の底変換の指定Arrow同型。 -/
def arcBaseChangeTransIso {A B T S : Type u}
    [CommRing A] [CommRing B] [CommRing T] [CommRing S]
    (f : A →+* B) (g : A →+* T) (h : T →+* S) (k : A →+* S)
    (hk : h.comp g = k) :
    Arrow.mk (CommRingCat.ofHom (arcBaseChangeHom f k)) ≅
      Arrow.mk (CommRingCat.ofHom (arcBaseChangeHom (arcBaseChangeHom f g) h)) := by
  subst k
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := h.toAlgebra
  letI : Algebra A S := (h.comp g).toAlgebra
  let X := Under.mk (CommRingCat.ofHom f)
  let G := CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of T)
  let H := CommRingCat.tensorProd (CommRingCat.of T) (CommRingCat.of S)
  let K := CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)
  let eg := CommRingCat.tensorProdIsoPushout (CommRingCat.of A) (CommRingCat.of T)
  let eh := CommRingCat.tensorProdIsoPushout (CommRingCat.of T) (CommRingCat.of S)
  let ek := CommRingCat.tensorProdIsoPushout (CommRingCat.of A) (CommRingCat.of S)
  let η : K ≅ G ⋙ H := ek ≪≫
    Under.pushoutComp (CommRingCat.ofHom g) (CommRingCat.ofHom h) ≪≫
    Functor.isoWhiskerRight eg.symm (Under.pushout (CommRingCat.ofHom h)) ≪≫
    Functor.isoWhiskerLeft G eh.symm
  let e := η.app X
  let q : Arrow.mk (K.obj X).hom ≅ Arrow.mk (H.obj (G.obj X)).hom :=
    Arrow.isoMk (Iso.refl _) ((Under.forget (CommRingCat.of S)).mapIso e) (by
      simpa using (Under.w e.hom).symm)
  exact q

end SerrePositivity.AlgebraicGeometry.ArcRouteB
