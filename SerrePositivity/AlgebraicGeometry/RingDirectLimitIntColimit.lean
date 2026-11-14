module

public import SerrePositivity.AlgebraicGeometry.LinearDirectLimitNaturality

/-!
概要：環の代数的順極限を、同じ系の整数加群の圏論的余極限として比較する。
方針：環の射の加法部分を整数線形に読み、既存の順極限比較を使う。
規約：環の順極限の台集合は変えず、標準の整数作用との同型を明示する。
使われ方：標準開の環の Frobenius 順極限を Čech 係数図式へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable (f : ∀ i j, i ≤ j → A i →+* A j)
variable [DirectedSystem A (f · · ·)]

/-- 環の有向系の実際の射を整数線形写像として読む。 -/
abbrev ringDirectSystemIntMap (i j : ℕ) (h : i ≤ j) : A i →ₗ[ℤ] A j :=
  (f i j h).toAddMonoidHom.toIntLinearMap

/-- 整数線形表示でも同じ有向系の法則が成り立つ。 -/
instance ringDirectSystemIntMap_directedSystem :
    DirectedSystem A (ringDirectSystemIntMap f · · ·) :=
  inferInstanceAs (DirectedSystem A (f · · ·))

/-- 環の順極限の加法群と、同じ整数加群の有向系の余極限との同型。 -/
def ringDirectLimitIntColimitIso :
    ModuleCat.of ℤ (DirectLimit A f) ≅
      colimit (linearDirectSystemFunctor (ringDirectSystemIntMap f)) := by
  let a : DirectLimit A f ≃+ DirectLimit A (ringDirectSystemIntMap f) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := by
        intro x y
        induction x, y using DirectLimit.induction₂ with
        | _ i x y =>
          rw [DirectLimit.add_def]
          exact (DirectLimit.add_def (f := ringDirectSystemIntMap f) i x y).symm }
  let b : ModuleCat.of ℤ (DirectLimit A f) ≅
      (linearDirectSystemCocone (ringDirectSystemIntMap f)).pt :=
    LinearEquiv.toModuleIso a.toIntLinearEquiv
  exact b ≪≫ linearDirectLimitColimitIso (ringDirectSystemIntMap f)

/-- 比較同型は有限段からの環の標準写像を、同じ余極限の標準写像へ送る。 -/
theorem ringDirectLimitIntColimitIso_of (n : ℕ) (x : A n) :
    (ringDirectLimitIntColimitIso f).hom.hom (DirectLimit.Ring.of A f n x) =
      (colimit.ι (linearDirectSystemFunctor (ringDirectSystemIntMap f)) n).hom x := by
  change (linearDirectLimitColimitIso (ringDirectSystemIntMap f)).hom.hom
      (DirectLimit.Module.of ℤ ℕ A (ringDirectSystemIntMap f) n x) = _
  exact congrArg (fun k ↦ k.hom x)
    (linearDirectLimitColimitIso_ι (ringDirectSystemIntMap f) n)

end SerrePositivity.AlgebraicGeometry
