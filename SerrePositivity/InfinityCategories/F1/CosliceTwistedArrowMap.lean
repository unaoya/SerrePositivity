module

public import SerrePositivity.InfinityCategories.F1.TwistedArrowProjection
public import SerrePositivity.InfinityCategories.F1.CoslicePinchedIso

/-!
概要：表現可能 coslice の錐を、左半分を固定した twisted arrow の単体へ写す。
方針：重みの左標準単体を一点へ潰し、右標準単体をそのまま保って元の錐と合成する。
規約：充填条件を仮定せず、全ての面・退化と左右の端点への厳密な可換性を示す。
使われ方：twisted arrow の一変数を固定した射影と、表現可能 fibration の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 左半分を標準一点へ潰し、右半分を保つ重みの射。 -/
def cosliceEdgewiseCollapse (n : SimplexCategory) :
    edgewiseWeight.{u}.obj n ⟶ join (Δ[0] : SSet.{u}) (stdSimplex.obj n) :=
  joinMap (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) (𝟙 _)

/-- 重みの崩壊写像は、全ての面・退化に自然。 -/
lemma cosliceEdgewiseCollapse_naturality {a b : SimplexCategory} (α : a ⟶ b) :
    edgewiseWeight.{u}.map α ≫ cosliceEdgewiseCollapse b =
      cosliceEdgewiseCollapse a ≫ joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.map α) := by
  change joinMap (SSet.opFunctor.map (stdSimplex.map α)) (stdSimplex.map α) ≫
    joinMap _ (𝟙 _) = joinMap _ (𝟙 _) ≫ joinMap (𝟙 _) (stdSimplex.map α)
  rw [← joinMap_comp, ← joinMap_comp]
  simp only [SSet.comp_const, Category.comp_id, Category.id_comp]

/-- 表現可能 coslice の錐を左端固定の twisted arrow の単体へ自然に写す。 -/
def cosliceTwistedArrowMap {C : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ C) :
    sliceUnder p ⟶ TwistedArrow C where
  app n := ↾fun s ↦ cosliceEdgewiseCollapse n.unop ≫ s.val
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    change cosliceEdgewiseCollapse m.unop ≫
      (joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.map α.unop) ≫ s.val) =
      edgewiseWeight.map α.unop ≫ (cosliceEdgewiseCollapse n.unop ≫ s.val)
    rw [← Category.assoc, ← cosliceEdgewiseCollapse_naturality, Category.assoc]

/-- 右端射影は、元の coslice の可変端点への射影そのもの。 -/
lemma cosliceTwistedArrowMap_right {C : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ C) :
    cosliceTwistedArrowMap p ≫ edgewiseRight C = sliceUnderProjection p := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (joinInr _ _ ≫ cosliceEdgewiseCollapse n.unop ≫ s.val) = _
  rw [cosliceEdgewiseCollapse, joinInr_joinMap_assoc, Category.id_comp]
  rfl

/-- 左端射影は元の coslice の固定頂点を反転した定値写像。 -/
lemma cosliceTwistedArrowMap_left {C : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ C) :
    cosliceTwistedArrowMap p ≫ edgewiseLeft C =
      SSet.const (SSet.opObjEquiv.symm (SSet.yonedaEquiv p)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply SSet.opObjEquiv.injective
  change SSet.yonedaEquiv ((stdSimplex.opIso ⦋n⦌).inv ≫ joinInl _ _ ≫
      cosliceEdgewiseCollapse ⦋n⦌ ≫ s.val) =
    SSet.opObjEquiv (PinchedHom.constant (SSet.opObjEquiv.symm (SSet.yonedaEquiv p)) n)
  rw [constant_opObjEquiv, cosliceEdgewiseCollapse, joinInl_joinMap_assoc]
  erw [s.property]
  rw [SSet.const_comp, SSet.comp_const]
  rfl

/-- 左半分の崩壊には各次数で切断があり、重みの射は全射。 -/
instance cosliceEdgewiseCollapse_epi (n : ℕ) : Epi (cosliceEdgewiseCollapse.{u} ⦋n⦌) := by
  let v : ((Δ[n] : SSet.{u}).op) _⦋0⦌ :=
    SSet.opObjEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)))
  let r : join (Δ[0] : SSet.{u}) Δ[n] ⟶ edgewiseWeight.obj ⦋n⦌ :=
    joinMap (SSet.const v) (𝟙 _)
  have hr : r ≫ cosliceEdgewiseCollapse ⦋n⦌ = 𝟙 _ := by
    change joinMap (SSet.const v) (𝟙 _) ≫ joinMap _ (𝟙 _) = _
    rw [← joinMap_comp]
    have h : SSet.const v ≫ SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) =
        𝟙 (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h, Category.id_comp, joinMap_id]
  exact epi_of_epi_fac hr

/-- 元の coslice の全ての単体は、比較後の twisted arrow の単体から一意に回収できる。 -/
instance cosliceTwistedArrowMap_mono {C : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ C) :
    Mono (cosliceTwistedArrowMap p) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro s t h
  apply Subtype.ext
  apply (cancel_epi (cosliceEdgewiseCollapse ⦋n⦌)).mp
  exact h

end SerrePositivity.InfinityCategories
