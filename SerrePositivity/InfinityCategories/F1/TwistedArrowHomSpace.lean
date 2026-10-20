module

public import SerrePositivity.InfinityCategories.F1.TwistedArrowLeftFibration
public import SerrePositivity.InfinityCategories.F1.CoslicePinchedIso

/-!
概要：twisted arrow 射影の固定両端の写像空間を、join の左右を固定した単体で記述する。
方針：実際の射影の vertex fiber を取り、両成分の条件を Yoneda と反転の同型で戻す。
規約：模型は元の twistedArrowProjection の fiber そのもので、quasicategory なら Kan 複体。
使われ方：表現可能射影との比較の各 fiber の写像空間での検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- twisted arrow の両端を指定頂点に固定した写像空間。 -/
def twistedArrowHomSpace {C : SSet.{u}} (x y : C _⦋0⦌) : SSet.{u} :=
  vertexFiber (twistedArrowProjection C) (SSet.opObjEquiv.symm x, y)

/-- 両端固定の twisted arrow の写像空間は Kan 複体。 -/
instance twistedArrowHomSpace_kanComplex {C : SSet.{u}} [Quasicategory C]
    (x y : C _⦋0⦌) : KanComplex (twistedArrowHomSpace x y) :=
  vertexFiber_kanComplex_of_leftFibration _ _

/-- fiber の単体を元の join の図式として読むと、左半分は始点に定値。 -/
lemma twistedArrowHomSpace_left {C : SSet.{u}} {x y : C _⦋0⦌} {n : ℕ}
    (s : (twistedArrowHomSpace x y) _⦋n⦌) :
    joinInl (Δ[n] : SSet.{u}).op Δ[n] ≫ s.val = SSet.const x := by
  have h := congrArg (fun z : (C.op ⊗ C) _⦋n⦌ ↦ SSet.opObjEquiv z.1) s.property
  change SSet.yonedaEquiv ((stdSimplex.opIso ⦋n⦌).inv ≫ joinInl _ _ ≫ s.val) =
    SSet.opObjEquiv (PinchedHom.constant (SSet.opObjEquiv.symm x) n) at h
  rw [constant_opObjEquiv] at h
  have he : (stdSimplex.opIso ⦋n⦌).inv ≫ joinInl _ _ ≫ s.val = SSet.const x := by
    apply SSet.yonedaEquiv.injective
    exact h
  have hh := congrArg (fun f ↦ (stdSimplex.opIso ⦋n⦌).hom ≫ f) he
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp, SSet.comp_const] using hh

/-- 同じ fiber の単体の右半分は終点に定値。 -/
lemma twistedArrowHomSpace_right {C : SSet.{u}} {x y : C _⦋0⦌} {n : ℕ}
    (s : (twistedArrowHomSpace x y) _⦋n⦌) :
    joinInr (Δ[n] : SSet.{u}).op Δ[n] ≫ s.val = SSet.const y := by
  have h := congrArg (fun z : (C.op ⊗ C) _⦋n⦌ ↦ z.2) s.property
  apply SSet.yonedaEquiv.injective
  exact h

/-- 左右を固定した join の図式を、元の射影の fiber の単体へ戻す。 -/
def twistedArrowHomSpaceSimplex {C : SSet.{u}} (x y : C _⦋0⦌) {n : ℕ}
    (F : edgewiseWeight.obj ⦋n⦌ ⟶ C)
    (hL : joinInl (Δ[n] : SSet.{u}).op Δ[n] ≫ F = SSet.const x)
    (hR : joinInr (Δ[n] : SSet.{u}).op Δ[n] ≫ F = SSet.const y) :
    (twistedArrowHomSpace x y) _⦋n⦌ := by
  refine ⟨F, ?_⟩
  apply Prod.ext
  · apply SSet.opObjEquiv.injective
    change SSet.yonedaEquiv ((stdSimplex.opIso ⦋n⦌).inv ≫ joinInl _ _ ≫ F) =
      SSet.opObjEquiv (PinchedHom.constant (SSet.opObjEquiv.symm x) n)
    rw [hL, SSet.comp_const, constant_opObjEquiv]
    rfl
  · change SSet.yonedaEquiv (joinInr _ _ ≫ F) = PinchedHom.constant y n
    rw [hR]
    rfl

/-- 元の射影の fiber と、左右の半分を固定した join の図式の全単射。 -/
def twistedArrowHomSpaceObjEquiv {C : SSet.{u}} (x y : C _⦋0⦌) (n : ℕ) :
    (twistedArrowHomSpace x y) _⦋n⦌ ≃
      {F : edgewiseWeight.obj ⦋n⦌ ⟶ C //
        joinInl (Δ[n] : SSet.{u}).op Δ[n] ≫ F = SSet.const x ∧
          joinInr (Δ[n] : SSet.{u}).op Δ[n] ≫ F = SSet.const y} where
  toFun s := ⟨s.val, twistedArrowHomSpace_left s, twistedArrowHomSpace_right s⟩
  invFun s := twistedArrowHomSpaceSimplex x y s.val s.property.1 s.property.2
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

end SerrePositivity.InfinityCategories
