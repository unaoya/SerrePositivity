module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseEndpoints
public import SerrePositivity.InfinityCategories.Core.VertexFiber

/-!
概要：底の恒等点上の全 twisted arrow 族を、元の同じ頂点 fiber の twisted arrow へ戻す。
方針：各重みからの射を元の fiber に持ち上げ、元の自然性をそのまま使う。
規約：全次数で厳密な底の条件を保持する。充填性は要求しない。
使われ方：大域評価の恒等点上の作用を、Kan fiber の左右の解像射影で判定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の頂点の恒等射を、twisted arrow の指定点として読む。 -/
def edgewiseIdentityPoint {B : SSet.{u}} (b : B _⦋0⦌) : (edgewiseSubdivision B) _⦋0⦌ :=
  SSet.const b

/-- 同じ恒等点の退化は、各重み上で元の頂点に定値な図式そのもの。 -/
lemma edgewiseIdentityPoint_constant {B : SSet.{u}} (b : B _⦋0⦌) (n : ℕ) :
    PinchedHom.constant (edgewiseIdentityPoint b) n =
      (SSet.const b : edgewiseWeight.obj ⦋n⦌ ⟶ B) := by
  change edgewiseWeight.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0) ≫ SSet.const b = SSet.const b
  exact SSet.comp_const _ _

/-- 同じ恒等点の右端は、指定した元の頂点。 -/
lemma edgewiseIdentityPoint_right {B : SSet.{u}} (b : B _⦋0⦌) :
    (edgewiseRight B).app (Opposite.op ⦋0⦌) (edgewiseIdentityPoint b) = b := by
  change SSet.yonedaEquiv (_ ≫ SSet.const b) = b
  rw [SSet.comp_const, ← SSet.yonedaEquiv_symm_zero, Equiv.apply_symm_apply]

/-- 底の恒等点上の全族を、元の同じ fiber の twisted arrow 全体へ持ち上げる。 -/
def edgewiseVertexFiberLift {A E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (f : A ⟶ edgewiseSubdivision E)
    (hf : f ≫ edgewiseSubdivisionMap p = SSet.const (edgewiseIdentityPoint b)) :
    A ⟶ edgewiseSubdivision (vertexFiber p b) where
  app n := ↾fun x ↦ vertexFiberLift p b (f.app n x) (by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hf n) x
    change (f.app n x) ≫ p = PinchedHom.constant (edgewiseIdentityPoint b) n.unop.len at h
    rw [edgewiseIdentityPoint_constant] at h
    exact h)
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro x
    apply vertexFiber_hom_ext p b
    exact ConcreteCategory.congr_hom (f.naturality α) x

/-- 持ち上げた同じ全族を元の全空間へ戻すと、元の全族そのもの。 -/
lemma edgewiseVertexFiberLift_map {A E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (f : A ⟶ edgewiseSubdivision E)
    (hf : f ≫ edgewiseSubdivisionMap p = SSet.const (edgewiseIdentityPoint b)) :
    edgewiseVertexFiberLift p b f hf ≫ edgewiseSubdivisionMap (vertexFiberι p b) = f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
