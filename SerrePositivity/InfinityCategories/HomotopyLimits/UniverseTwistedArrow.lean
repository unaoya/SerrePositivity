module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseEdgewiseWeight
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.Projection

/-!
概要：元の twisted arrow 単体集合の宇宙持ち上げと、持ち上げた元の圏のものを同定する。
方針：同じ重みの宇宙同型と、全写像の宇宙持ち上げの充満忠実性を使う。
規約：任意次数の全単体と全単体作用を保持する。
使われ方：共同 Hom 図式と全 Yoneda 関手の宇宙比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の twisted arrow の全単体を、同じ大きい宇宙の重み上の全写像へ移す。 -/
def uliftTwistedArrowSimplexEquiv (C : SSet.{u}) (n : ℕ) :
    ((SSet.uliftFunctor.{v, u}).obj (TwistedArrow C)) _⦋n⦌ ≃
      (TwistedArrow ((SSet.uliftFunctor.{v, u}).obj C)) _⦋n⦌ where
  toFun s := (edgewiseWeightUniverseIso.{u, v} n).inv ≫
    (SSet.uliftFunctor.{v, u}).map s.down
  invFun t := ULift.up ((SSet.uliftFunctor.{v, u}).preimage
    ((edgewiseWeightUniverseIso.{u, v} n).hom ≫ t))
  left_inv s := by
    apply ULift.ext
    apply (SSet.uliftFunctor.{v, u}).map_injective
    rw [Functor.map_preimage, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  right_inv t := by
    change (edgewiseWeightUniverseIso.{u, v} n).inv ≫
      (SSet.uliftFunctor.{v, u}).map ((SSet.uliftFunctor.{v, u}).preimage
        ((edgewiseWeightUniverseIso.{u, v} n).hom ≫ t)) = t
    rw [Functor.map_preimage, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 元の全 twisted arrow の宇宙持ち上げを、同じ圏の宇宙持ち上げのものへ比較する同型。 -/
def uliftTwistedArrowIso (C : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj (TwistedArrow C) ≅
      TwistedArrow ((SSet.uliftFunctor.{v, u}).obj C) :=
  NatIso.ofComponents (fun n => Equiv.toIso (uliftTwistedArrowSimplexEquiv C n.unop.len))
    (fun {m n} α => by
      rcases m with ⟨⟨m⟩⟩
      rcases n with ⟨⟨n⟩⟩
      apply ConcreteCategory.hom_ext
      rintro ⟨f⟩
      change (edgewiseWeightUniverseIso.{u, v} _).inv ≫
          (SSet.uliftFunctor.{v, u}).map (edgewiseWeight.map α.unop ≫ f) =
        edgewiseWeight.map α.unop ≫ ((edgewiseWeightUniverseIso.{u, v} _).inv ≫
          (SSet.uliftFunctor.{v, u}).map f)
      simp only [Functor.map_comp, ← Category.assoc]
      rw [edgewiseWeightUniverseIso_inv_map.{u, v} α.unop])

/-- 元の同型は、各全単体を同じ重みの宇宙比較に沿う元の全写像へ厳密に送る。 -/
lemma uliftTwistedArrowIso_hom_app (C : SSet.{u}) {n : ℕ}
    (f : (TwistedArrow C) _⦋n⦌) :
    (uliftTwistedArrowIso.{u, v} C).hom.app (Opposite.op ⦋n⦌) (ULift.up f) =
      (edgewiseWeightUniverseIso.{u, v} n).inv ≫ (SSet.uliftFunctor.{v, u}).map f := rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
