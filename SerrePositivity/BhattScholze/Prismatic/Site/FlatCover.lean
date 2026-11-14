module
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Composition

public import SerrePositivity.BhattScholze.Prismatic.Site.PrismOver
public import SerrePositivity.BhattScholze.Prism.Basic.Category
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Identity
public import SerrePositivity.HomologicalAlgebra.Cech.Basic
import SerrePositivity.HomologicalAlgebra.Cech.Composition

/-!
# 有界 prism の忠実平坦な被覆

## 概要
prism の射の完全忠実平坦性は、同型と合成で保たれる。

## 方針
prism イデアルの剛性と、加群の完全忠実平坦性の合成を使う。
通常の忠実平坦な環射の Čech 完全性は、自己底変換で分裂することから得る。

## 規約
BS 著者版 Corollary 3.12 (a) と、(c) の有限剰余で使う環の Čech 完全性。

## 使われ方
固定基底の prismatic site の平坦位相。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open CategoryTheory

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}

namespace PrismOver

/-- (p,d) 完全忠実平坦性で表した prismatic site の被覆（BS 著者版 Corollary 3.12 (a)）。 -/
abbrev IsFaithfullyFlat {X Y : PrismOver P R κ} (f : X ⟶ Y) : Prop :=
  f.toHom.IsFaithfullyFlat

/-- 同型は prismatic site の忠実平坦な被覆。 -/
theorem isFaithfullyFlat_of_isIso {X Y : PrismOver P R κ} (f : X ⟶ Y) [IsIso f] :
    IsFaithfullyFlat f := by
  let g := f.toHom.toRingHom
  let h := (inv f).toHom.toRingHom
  have h₁ : g.comp h = RingHom.id Y.B :=
    congrArg (fun k : Y ⟶ Y ↦ k.toHom.toRingHom) (IsIso.inv_hom_id f)
  have h₂ : h.comp g = RingHom.id X.B :=
    congrArg (fun k : X ⟶ X ↦ k.toHom.toRingHom) (IsIso.hom_inv_id f)
  let e := RingEquiv.ofRingHom g h h₁ h₂
  let := g.toAlgebra
  let l : X.B ≃ₗ[X.B] Y.B :=
    { e.toAddEquiv with
      map_smul' := fun r x ↦ e.map_mul r x }
  exact isCompletelyFaithfullyFlat_of_linearEquiv _ l (Andre.Transfinite.isCompletelyFaithfullyFlat_self _ _)

/-- 忠実平坦な被覆の合成は忠実平坦。 -/
theorem IsFaithfullyFlat.comp {X Y Z : PrismOver P R κ} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsFaithfullyFlat f) (hg : IsFaithfullyFlat g) : IsFaithfullyFlat (f ≫ g) := by
  let I := Ideal.span {(p : X.B), X.Q.generator}
  have hm : I.map f.toHom.toRingHom = Ideal.span {(p : Y.B), Y.Q.generator} := by
    change (Ideal.span {(p : X.B), X.Q.generator}).map f.toHom.toRingHom = _
    rw [← Set.singleton_union, Ideal.span_union, Ideal.map_sup, Ideal.map_span,
      Set.image_singleton, map_natCast]
    change Ideal.span {(p : Y.B)} ⊔ X.Q.ideal.map f.toHom.toRingHom = _
    rw [f.toHom.map_ideal_eq, OrientedPrism.ideal, ← Ideal.span_union, Set.singleton_union]
  apply Andre.Transfinite.isCompletelyFaithfullyFlat_comp f.toHom.toRingHom g.toHom.toRingHom I hf
  rw [hm]
  exact hg

end PrismOver

end SerrePositivity.BhattScholze.Prismatic

namespace SerrePositivity.Cech

open CategoryTheory

/-- 概要：忠実平坦な環射の増大 Čech 複体は全次数で完全。
方針：自分自身に沿う底変換で分裂し、忠実平坦性が完全性を反映する。
規約：通常のテンソル冪。BS 著者版 Corollary 3.12 (c) の有限剰余に使う。
使われ方：完備 Čech の有限段での完全性。 -/
theorem isCechExact_of_faithfullyFlat {A : CommRingCat.{u}} (B : Under A)
    : letI := B.hom.hom.toAlgebra
      Module.FaithfullyFlat A B.right → IsCechExact (Arrow.mk B.hom) := by
  let := B.hom.hom.toAlgebra
  intro h
  exact (isCechExact_baseChange_iff B.right B).mp (isCechExact_baseChange_of_map B B (𝟙 B))

end SerrePositivity.Cech
