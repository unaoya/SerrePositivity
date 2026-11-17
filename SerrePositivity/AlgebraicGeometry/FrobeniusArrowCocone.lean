module

public import SerrePositivity.AlgebraicGeometry.FrobeniusArrowDiagramMaps

/-!
概要：実際の Frobenius 順極限の環の矢印は、既存の矢印の反復系の余極限。
方針：同じ有限段の写像の余錐と、環の lift・hom_ext の普遍性を使う。
規約：元の矢印と二つの端点の環準同型を保持する。
使われ方：B1 の conerve の余極限保存を実際の Frobenius の係数へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable (f : Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
variable (hA : (p : f.left) = 0) (hB : (p : f.right) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 実際の順極限の矢印を点とし、元の有限段の二つの標準写像を持つ余錐。 -/
def frobeniusArrowCocone : Cocone (frobeniusArrowDiagram f p hp hA hB) where
  pt := Arrow.mk (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hA hB f.hom.hom))
  ι :=
    { app := fun n ↦ Arrow.homMk
        (CommRingCat.ofHom (frobeniusDirectLimitOf f.left p hp hA n))
        (CommRingCat.ofHom (frobeniusDirectLimitOf f.right p hp hB n)) (by
          apply CommRingCat.hom_ext
          apply RingHom.ext
          intro x
          exact frobeniusDirectLimitMap_of p hp hA hB f.hom.hom n x)
      naturality := by
        intro i j a
        apply Arrow.hom_ext
        · change ((frobeniusArrowDiagram f p hp hA hB).map a).left ≫
            CommRingCat.ofHom (frobeniusDirectLimitOf f.left p hp hA j) =
              CommRingCat.ofHom (frobeniusDirectLimitOf f.left p hp hA i) ≫ 𝟙 _
          rw [frobeniusArrowDiagram_map_left]
          apply CommRingCat.hom_ext
          apply RingHom.ext
          intro x
          exact DirectLimit.Ring.of_f (G := fun _ : ℕ ↦ f.left)
            (f := frobeniusDirectSystemMap f.left p hp hA) (leOfHom a) x
        · change ((frobeniusArrowDiagram f p hp hA hB).map a).right ≫
            CommRingCat.ofHom (frobeniusDirectLimitOf f.right p hp hB j) =
              CommRingCat.ofHom (frobeniusDirectLimitOf f.right p hp hB i) ≫ 𝟙 _
          rw [frobeniusArrowDiagram_map_right]
          apply CommRingCat.hom_ext
          apply RingHom.ext
          intro x
          exact DirectLimit.Ring.of_f (G := fun _ : ℕ ↦ f.right)
            (f := frobeniusDirectSystemMap f.right p hp hB) (leOfHom a) x }

set_option backward.isDefEq.respectTransparency false in
/-- 同じ二つの環の普遍性は、実際の矢印の余極限の普遍性を与える。 -/
def frobeniusArrowIsColimit : IsColimit (frobeniusArrowCocone f p hp hA hB) where
  desc c := Arrow.homMk
    (CommRingCat.ofHom (DirectLimit.Ring.lift _
      (frobeniusDirectSystemMap f.left p hp hA) c.pt.left
      (fun n ↦ (c.ι.app n).left.hom) (by
        intro i j h x
        have hw : ((frobeniusArrowDiagram f p hp hA hB).map (homOfLE h)).left ≫
            (c.ι.app j).left = (c.ι.app i).left :=
          congrArg Arrow.Hom.left (c.w (homOfLE h))
        rw [frobeniusArrowDiagram_map_left] at hw
        exact congrArg (fun k : f.left ⟶ c.pt.left ↦ k.hom x) hw)))
    (CommRingCat.ofHom (DirectLimit.Ring.lift _
      (frobeniusDirectSystemMap f.right p hp hB) c.pt.right
      (fun n ↦ (c.ι.app n).right.hom) (by
        intro i j h x
        have hw : ((frobeniusArrowDiagram f p hp hA hB).map (homOfLE h)).right ≫
            (c.ι.app j).right = (c.ι.app i).right :=
          congrArg Arrow.Hom.right (c.w (homOfLE h))
        rw [frobeniusArrowDiagram_map_right] at hw
        exact congrArg (fun k : f.right ⟶ c.pt.right ↦ k.hom x) hw))) (by
      apply CommRingCat.hom_ext
      apply DirectLimit.Ring.hom_ext
      intro n
      apply RingHom.ext
      intro x
      change c.pt.hom.hom ((c.ι.app n).left.hom x) =
        (c.ι.app n).right.hom (f.hom.hom x)
      exact congrArg (fun k : f.left ⟶ c.pt.right ↦ k.hom x) (c.ι.app n).w)
  fac c n := by
    apply Arrow.hom_ext
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      rfl
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      rfl
  uniq c m hm := by
    apply Arrow.hom_ext
    · apply CommRingCat.hom_ext
      apply DirectLimit.Ring.hom_ext
      intro n
      apply RingHom.ext
      intro x
      exact congrArg (fun k : f ⟶ c.pt ↦ k.left.hom x) (hm n)
    · apply CommRingCat.hom_ext
      apply DirectLimit.Ring.hom_ext
      intro n
      apply RingHom.ext
      intro x
      exact congrArg (fun k : f ⟶ c.pt ↦ k.right.hom x) (hm n)

/-- 同じ実際の矢印の余錐を、B1 と同じ小さい添字へ移す。 -/
def frobeniusArrowSmallCocone : Cocone (frobeniusArrowSmallDiagram f p hp hA hB) :=
  (frobeniusArrowCocone f p hp hA hB).whisker AsSmall.down

/-- 添字の同値による移送は、同じ実際の余錐の余極限の普遍性を保つ。 -/
def frobeniusArrowSmallIsColimit : IsColimit (frobeniusArrowSmallCocone f p hp hA hB) :=
  (frobeniusArrowIsColimit f p hp hA hB).whiskerEquivalence
    (AsSmall.equiv : ℕ ≌ AsSmall.{u} ℕ).symm

/-- 実際の Frobenius 順極限の矢印と、B1 の同じ矢印の余極限の標準同型。 -/
def frobeniusArrowSmallColimitIso :
    Arrow.mk (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hA hB f.hom.hom)) ≅
      colimit (frobeniusArrowSmallDiagram f p hp hA hB) :=
  (frobeniusArrowSmallIsColimit f p hp hA hB).coconePointUniqueUpToIso
    (colimit.isColimit (frobeniusArrowSmallDiagram f p hp hA hB))

end SerrePositivity.AlgebraicGeometry
