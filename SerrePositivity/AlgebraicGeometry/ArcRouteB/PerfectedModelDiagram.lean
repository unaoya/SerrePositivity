module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.ModelUnder
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.FrobeniusPerfect

/-!
概要：同じ有限表示模型の各終域を実際のFrobenius順極限へ送り、元の基底を保つ。
方針：同じSmallModelの射をFrobeniusの関手性で送り、各段0の射で構造射を定める。
規約：対象・脚の選択をやり直さず、基底の完全性を仮定した元の型を保つ。
使われ方：2iのM08、BM18 Proposition 4.8(1)の完全化した模型。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 計画M08：同じ有限表示模型の指定したFrobenius順極限の図式。 -/
def perfectedModelDiagram (p : ℕ) [Fact p.Prime]
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [PerfectRing A p] (hp : (p : A) = 0) :
    FinitePresentationModelIndex A B ⥤ Under (CommRingCat.of A) := by
  let D := finitePresentationModelUnderDiagram A B
  let hz (j : FinitePresentationModelIndex A B) : (p : (D.obj j).right) = 0 := by
    rw [← map_natCast (D.obj j).hom.hom, hp, map_zero]
  let i (j : FinitePresentationModelIndex A B) :=
    frobeniusDirectLimitOf (D.obj j).right p (Fact.out : p.Prime) (hz j) 0
  refine
    { obj := fun j ↦ Under.mk (CommRingCat.ofHom ((i j).comp (D.obj j).hom.hom))
      map := fun {j k} f ↦ Under.homMk
        (CommRingCat.ofHom (frobeniusDirectLimitMap p (Fact.out : p.Prime)
          (hz j) (hz k) (D.map f).right.hom)) ?_
      map_id := ?_
      map_comp := ?_ }
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change frobeniusDirectLimitMap p (Fact.out : p.Prime) (hz j) (hz k)
      (D.map f).right.hom (frobeniusDirectLimitOf (D.obj j).right p
        (Fact.out : p.Prime) (hz j) 0 ((D.obj j).hom.hom a)) =
      frobeniusDirectLimitOf (D.obj k).right p (Fact.out : p.Prime) (hz k) 0
        ((D.obj k).hom.hom a)
    rw [frobeniusDirectLimitMap_of]
    exact congrArg (frobeniusDirectLimitOf (D.obj k).right p (Fact.out : p.Prime) (hz k) 0)
      (RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Under.w (D.map f))) a)
  · intro j
    ext : 1
    apply CommRingCat.hom_ext
    change frobeniusDirectLimitMap p (Fact.out : p.Prime) (hz j) (hz j)
      (D.map (𝟙 j)).right.hom = _
    rw [D.map_id]
    exact frobeniusDirectLimitMap_id p (Fact.out : p.Prime) (hz j)
  · intro j k l f g
    ext : 1
    apply CommRingCat.hom_ext
    change frobeniusDirectLimitMap p (Fact.out : p.Prime) (hz j) (hz l)
      (D.map (f ≫ g)).right.hom = _
    rw [D.map_comp]
    exact (frobeniusDirectLimitMap_comp p (Fact.out : p.Prime) (hz j) (hz k)
      (D.map f).right.hom (hz l) (D.map g).right.hom).symm

end SerrePositivity.AlgebraicGeometry.ArcRouteB
