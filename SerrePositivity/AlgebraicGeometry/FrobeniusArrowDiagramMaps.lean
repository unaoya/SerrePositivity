module

public import SerrePositivity.AlgebraicGeometry.RingDirectLimitCocone
public import SerrePositivity.AlgebraicGeometry.AffineFrobeniusCechExact

/-!
概要：既存の Frobenius の矢印の反復系の射を、同じ環の有向系の射と照合する。
方針：単位成分の自然変換の可換性を、後続射から全ての射へ渡す。
規約：既存の Functor.ofSequence の矢印の図式を変更しない。
使われ方：実際の Frobenius 順極限の矢印の普遍性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable (f : Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
variable (hA : (p : f.left) = 0) (hB : (p : f.right) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 既存の矢印の反復系の左成分は、同じ環の任意の段の Frobenius の射。 -/
theorem frobeniusArrowDiagram_map_left {i j : ℕ} (a : i ⟶ j) :
    ((frobeniusArrowDiagram f p hp hA hB).map a).left =
      CommRingCat.ofHom (frobeniusDirectSystemMap f.left p hp hA i j (leOfHom a)) := by
  let t : ringDirectSystemFunctor (frobeniusDirectSystemMap f.left p hp hA) ⟶
      frobeniusArrowDiagram f p hp hA hB ⋙ Arrow.leftFunc :=
    NatTrans.ofSequence (fun _ ↦ 𝟙 f.left) (by
      intro n
      change CommRingCat.ofHom (frobeniusDirectSystemMap f.left p hp hA n (n + 1) (n.le_add_right 1)) ≫ 𝟙 _ =
        𝟙 _ ≫ ((frobeniusArrowDiagram f p hp hA hB).map (homOfLE (n.le_add_right 1))).left
      change CommRingCat.ofHom (frobeniusDirectSystemMap f.left p hp hA n (n + 1) (n.le_add_right 1)) ≫ 𝟙 _ =
        𝟙 _ ≫ ((Functor.ofSequence (fun _ : ℕ ↦ frobeniusArrowStep f p hp hA hB)).map
          (homOfLE (n.le_add_right 1))).left
      rw [Functor.ofSequence_map_homOfLE_succ]
      simp only [Category.comp_id, Category.id_comp]
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      change frobeniusDirectSystemMap f.left p hp hA n (n + 1) (n.le_add_right 1) x =
        frobeniusDirectSystemMap f.left p hp hA 0 1 (by decide) x
      rw [frobeniusDirectSystemMap_apply, frobeniusDirectSystemMap_apply]
      simp)
  have h := t.naturality a
  change CommRingCat.ofHom (frobeniusDirectSystemMap f.left p hp hA i j (leOfHom a)) ≫ 𝟙 _ =
    𝟙 _ ≫ ((frobeniusArrowDiagram f p hp hA hB).map a).left at h
  exact ((Category.comp_id (CommRingCat.ofHom
    (frobeniusDirectSystemMap f.left p hp hA i j (leOfHom a)))).symm.trans
      (h.trans (Category.id_comp (((frobeniusArrowDiagram f p hp hA hB).map a).left)))).symm

set_option backward.isDefEq.respectTransparency false in
/-- 既存の矢印の反復系の右成分も、同じ環の任意の段の Frobenius の射。 -/
theorem frobeniusArrowDiagram_map_right {i j : ℕ} (a : i ⟶ j) :
    ((frobeniusArrowDiagram f p hp hA hB).map a).right =
      CommRingCat.ofHom (frobeniusDirectSystemMap f.right p hp hB i j (leOfHom a)) := by
  let t : ringDirectSystemFunctor (frobeniusDirectSystemMap f.right p hp hB) ⟶
      frobeniusArrowDiagram f p hp hA hB ⋙ Arrow.rightFunc :=
    NatTrans.ofSequence (fun _ ↦ 𝟙 f.right) (by
      intro n
      change CommRingCat.ofHom (frobeniusDirectSystemMap f.right p hp hB n (n + 1) (n.le_add_right 1)) ≫ 𝟙 _ =
        𝟙 _ ≫ ((frobeniusArrowDiagram f p hp hA hB).map (homOfLE (n.le_add_right 1))).right
      change CommRingCat.ofHom (frobeniusDirectSystemMap f.right p hp hB n (n + 1) (n.le_add_right 1)) ≫ 𝟙 _ =
        𝟙 _ ≫ ((Functor.ofSequence (fun _ : ℕ ↦ frobeniusArrowStep f p hp hA hB)).map
          (homOfLE (n.le_add_right 1))).right
      rw [Functor.ofSequence_map_homOfLE_succ]
      simp only [Category.comp_id, Category.id_comp]
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      change frobeniusDirectSystemMap f.right p hp hB n (n + 1) (n.le_add_right 1) x =
        frobeniusDirectSystemMap f.right p hp hB 0 1 (by decide) x
      rw [frobeniusDirectSystemMap_apply, frobeniusDirectSystemMap_apply]
      simp)
  have h := t.naturality a
  change CommRingCat.ofHom (frobeniusDirectSystemMap f.right p hp hB i j (leOfHom a)) ≫ 𝟙 _ =
    𝟙 _ ≫ ((frobeniusArrowDiagram f p hp hA hB).map a).right at h
  exact ((Category.comp_id (CommRingCat.ofHom
    (frobeniusDirectSystemMap f.right p hp hB i j (leOfHom a)))).symm.trans
      (h.trans (Category.id_comp (((frobeniusArrowDiagram f p hp hA hB).map a).right)))).symm

end SerrePositivity.AlgebraicGeometry
