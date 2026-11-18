module

public import SerrePositivity.AlgebraicGeometry.FrobeniusArrowCocone

/-!
概要：実際の Frobenius の矢印と余極限の標準比較の自然性。
方針：元の可換な四角形を各有限段に使い、同じ標準脚で照合する。
規約：両端だけでなく矢印全体とその有限段の射を保持する。
使われ方：同じ増大 conerve の比較を、係数と閉中心の射に自然に渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {f g : Arrow CommRingCat.{u}} (F : f ⟶ g) (p : ℕ) (hp : p.Prime)
variable (hA : (p : f.left) = 0) (hB : (p : f.right) = 0)
variable (hC : (p : g.left) = 0) (hD : (p : g.right) = 0)

/-- 元の可換な四角形の両端の実際の Frobenius 順極限が与える矢印の射。 -/
def frobeniusDirectLimitArrowMap :
    Arrow.mk (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hA hB f.hom.hom)) ⟶
      Arrow.mk (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hC hD g.hom.hom)) :=
  Arrow.homMk
    (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hA hC F.left.hom))
    (CommRingCat.ofHom (frobeniusDirectLimitMap p hp hB hD F.right.hom)) (by
      apply CommRingCat.hom_ext
      apply DirectLimit.Ring.hom_ext
      intro n
      apply RingHom.ext
      intro x
      change frobeniusDirectLimitOf g.right p hp hD n (g.hom.hom (F.left.hom x)) =
        frobeniusDirectLimitOf g.right p hp hD n (F.right.hom (f.hom.hom x))
      exact congrArg (frobeniusDirectLimitOf g.right p hp hD n)
        (congrArg (fun k : f.left ⟶ g.right ↦ k.hom x) F.w))

set_option backward.isDefEq.respectTransparency false in
/-- 元の四角形は、同じ有限段の Frobenius の反復図式の自然変換。 -/
def frobeniusArrowDiagramMap :
    frobeniusArrowDiagram f p hp hA hB ⟶ frobeniusArrowDiagram g p hp hC hD :=
  NatTrans.ofSequence (fun _ ↦ F) (by
    intro n
    change (Functor.ofSequence (fun _ : ℕ ↦ frobeniusArrowStep f p hp hA hB)).map
        (homOfLE (n.le_add_right 1)) ≫ F =
      F ≫ (Functor.ofSequence (fun _ : ℕ ↦ frobeniusArrowStep g p hp hC hD)).map
        (homOfLE (n.le_add_right 1))
    rw [Functor.ofSequence_map_homOfLE_succ, Functor.ofSequence_map_homOfLE_succ]
    apply Arrow.hom_ext
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      exact frobeniusDirectSystemMap_naturality p hp hA hC F.left.hom 0 1 (by decide) x
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      exact frobeniusDirectSystemMap_naturality p hp hB hD F.right.hom 0 1 (by decide) x)

/-- B1 と同じ小さい添字での、元の有限段の四角形の自然変換。 -/
def frobeniusArrowSmallDiagramMap :
    frobeniusArrowSmallDiagram f p hp hA hB ⟶
      frobeniusArrowSmallDiagram g p hp hC hD :=
  Functor.whiskerLeft AsSmall.down (frobeniusArrowDiagramMap F p hp hA hB hC hD)

/-- 標準同型は、同じ有限段からの矢印の標準脚を保つ。 -/
theorem frobeniusArrowSmallColimitIso_ι (n : AsSmall.{u} ℕ) :
    (frobeniusArrowSmallCocone f p hp hA hB).ι.app n ≫
        (frobeniusArrowSmallColimitIso f p hp hA hB).hom =
      colimit.ι (frobeniusArrowSmallDiagram f p hp hA hB) n :=
  (frobeniusArrowSmallIsColimit f p hp hA hB).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (frobeniusArrowSmallDiagram f p hp hA hB)) n

set_option backward.isDefEq.respectTransparency false in
/-- 実際の余錐の脚と、元の四角形の Frobenius 順極限の射は可換。 -/
theorem frobeniusArrowCocone_map (n : AsSmall.{u} ℕ) :
    (frobeniusArrowSmallCocone f p hp hA hB).ι.app n ≫
        frobeniusDirectLimitArrowMap F p hp hA hB hC hD =
      (frobeniusArrowSmallDiagramMap F p hp hA hB hC hD).app n ≫
        (frobeniusArrowSmallCocone g p hp hC hD).ι.app n := by
  apply Arrow.hom_ext
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rfl
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- 同じ実際の矢印と圏論的余極限の標準比較は、元の四角形に自然。 -/
theorem frobeniusArrowSmallColimitIso_naturality :
    frobeniusDirectLimitArrowMap F p hp hA hB hC hD ≫
        (frobeniusArrowSmallColimitIso g p hp hC hD).hom =
      (frobeniusArrowSmallColimitIso f p hp hA hB).hom ≫
        colim.map (frobeniusArrowSmallDiagramMap F p hp hA hB hC hD) := by
  apply (frobeniusArrowSmallIsColimit f p hp hA hB).hom_ext
  intro n
  rw [← Category.assoc, frobeniusArrowCocone_map, Category.assoc,
    frobeniusArrowSmallColimitIso_ι]
  rw [← Category.assoc, frobeniusArrowSmallColimitIso_ι]
  exact (colimit.ι_map (frobeniusArrowSmallDiagramMap F p hp hA hB hC hD) n).symm

end SerrePositivity.AlgebraicGeometry
