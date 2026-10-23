module

public import SerrePositivity.InfinityCategories.F1.Joins.CosliceSimplexExpansion
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.HomSpace
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanLimits

/-!
概要：両端固定の join の写像空間を、左と右の単体の大きさを分けた二重単体図式にする。
方針：各行を左右定値の join 図式で表示し、coslice fiber との厳密な同型を保つ。
規約：左の添字も反転した標準単体の前合成で動かし、面・退化を全て扱う。
使われ方：各行の比較同値を元の twisted arrow の対角へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 左の標準単体を固定した、左右定値の join 図式の行。 -/
def twistedHomRow {C : SSet.{u}} (x y : C _⦋0⦌) (m : SimplexCategory) : SSet.{u} where
  obj n := {F : join (stdSimplex.obj m).op (stdSimplex.obj n.unop) ⟶ C //
    joinInl _ _ ≫ F = SSet.const x ∧ joinInr _ _ ≫ F = SSet.const y}
  map α := ↾fun F ↦ ⟨joinMap (𝟙 _) (stdSimplex.map α.unop) ≫ F.val, by
    constructor
    · rw [← Category.assoc, joinInl_joinMap, Category.id_comp, F.property.1]
    · rw [← Category.assoc, joinInr_joinMap, Category.assoc, F.property.2, SSet.comp_const]⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    change joinMap (𝟙 _) (stdSimplex.map (𝟙 n.unop)) ≫ F.val = F.val
    rw [CategoryTheory.Functor.map_id, joinMap_id, Category.id_comp]
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    change joinMap (𝟙 _) (stdSimplex.map (β.unop ≫ α.unop)) ≫ F.val =
      joinMap (𝟙 _) (stdSimplex.map β.unop) ≫
        (joinMap (𝟙 _) (stdSimplex.map α.unop) ≫ F.val)
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, ← joinMap_comp, Category.id_comp]

/-- 左の添字の射による行の前合成。 -/
def twistedHomRowMap {C : SSet.{u}} (x y : C _⦋0⦌) {m n : SimplexCategory}
    (α : m ⟶ n) : twistedHomRow x y n ⟶ twistedHomRow x y m where
  app d := ↾fun F ↦ ⟨joinMap (SSet.opFunctor.map (stdSimplex.map α)) (𝟙 _) ≫ F.val, by
    constructor
    · rw [← Category.assoc, joinInl_joinMap, Category.assoc, F.property.1, SSet.comp_const]
    · rw [← Category.assoc, joinInr_joinMap, Category.id_comp, F.property.2]⟩
  naturality {d e} β := by
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    change joinMap (SSet.opFunctor.map (stdSimplex.map α)) (𝟙 _) ≫
      (joinMap (𝟙 _) (stdSimplex.map β.unop) ≫ F.val) =
      joinMap (𝟙 _) (stdSimplex.map β.unop) ≫
        (joinMap (SSet.opFunctor.map (stdSimplex.map α)) (𝟙 _) ≫ F.val)
    simp only [← Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id]

/-- 両方の添字を別々に動かす二重単体図式。 -/
def twistedHomRows {C : SSet.{u}} (x y : C _⦋0⦌) : SimplexCategoryᵒᵖ ⥤ SSet.{u} where
  obj n := twistedHomRow x y n.unop
  map α := twistedHomRowMap x y α.unop
  map_id n := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    change joinMap (SSet.opFunctor.map (stdSimplex.map (𝟙 n.unop))) (𝟙 _) ≫ F.val = F.val
    rw [CategoryTheory.Functor.map_id, SSet.opFunctor.map_id, joinMap_id, Category.id_comp]
  map_comp α β := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro F
    apply Subtype.ext
    change joinMap (SSet.opFunctor.map (stdSimplex.map (β.unop ≫ α.unop))) (𝟙 _) ≫ F.val =
      joinMap (SSet.opFunctor.map (stdSimplex.map β.unop)) (𝟙 _) ≫
        (joinMap (SSet.opFunctor.map (stdSimplex.map α.unop)) (𝟙 _) ≫ F.val)
    rw [CategoryTheory.Functor.map_comp, SSet.opFunctor.map_comp,
      ← Category.assoc, ← joinMap_comp, Category.id_comp]

/-- 各行は、左の固定単体を広げた実際の coslice fiber と厳密に同型。 -/
def twistedHomRowCosliceIso {C : SSet.{u}} (x y : C _⦋0⦌) (m : SimplexCategory) :
    twistedHomRow x y m ≅
      vertexFiber (sliceUnderProjection (cosliceSimplexCollapse m ≫ SSet.yonedaEquiv.symm x)) y :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso
    { toFun := fun F ↦ ⟨⟨F.val, F.property.1.trans (cosliceSimplexCollapse_comp_yoneda x m).symm⟩,
        by
          change SSet.yonedaEquiv (joinInr _ _ ≫ F.val) = PinchedHom.constant y n.unop.len
          rw [F.property.2]
          rfl⟩
      invFun := fun F ↦ ⟨F.val.val, F.val.property.trans (cosliceSimplexCollapse_comp_yoneda x m),
        by
          apply SSet.yonedaEquiv.injective
          exact F.property⟩
      left_inv _ := Subtype.ext rfl
      right_inv _ := Subtype.ext (Subtype.ext rfl) }) (by
        intro n m α
        apply ConcreteCategory.hom_ext
        intro F
        rfl)

/-- 元の coslice の錐を、左の固定単体を広げた各行へ送る。 -/
def twistedHomRowAugment {C : SSet.{u}} (x y : C _⦋0⦌) (m : SimplexCategory) :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y ⟶ twistedHomRow x y m :=
  cosliceRestrictionFiberMap (SSet.yonedaEquiv.symm x) (cosliceSimplexCollapse m) y ≫
    (twistedHomRowCosliceIso x y m).inv

/-- 行の拡張の実際の式は、左の形を一点へ潰す joinMap による前合成。 -/
lemma twistedHomRowAugment_app_val {C : SSet.{u}} (x y : C _⦋0⦌)
    (m : SimplexCategory) (n : SimplexCategoryᵒᵖ)
    (F : (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y).obj n) :
    ((twistedHomRowAugment x y m).app n F).val =
      joinMap (cosliceSimplexCollapse m) (𝟙 (stdSimplex.obj n.unop)) ≫ F.val.val := rfl

/-- 左の固定単体を広げた各行も Kan 複体。 -/
instance twistedHomRow_kanComplex {C : SSet.{u}} [Quasicategory C]
    (x y : C _⦋0⦌) (m : SimplexCategory) : KanComplex (twistedHomRow x y m) := by
  have : KanComplex (vertexFiber
      (sliceUnderProjection (cosliceSimplexCollapse m ≫ SSet.yonedaEquiv.symm x)) y) :=
    vertexFiber_kanComplex_of_leftFibration _ _
  exact HomotopyLimits.kanComplex_of_iso (twistedHomRowCosliceIso x y m).symm

/-- 各行の拡張は元の coslice の写像空間の同値。 -/
lemma twistedHomRowAugment_isQCatEquivalence {C : SSet.{u}} [Quasicategory C]
    (x y : C _⦋0⦌) (m : ℕ) :
    IsQCatEquivalence (twistedHomRowAugment x y ⦋m⦌) := by
  exact (cosliceSimplexExpansion_isQCatEquivalence x y m).comp
    (qCatEquivalenceOfIso (twistedHomRowCosliceIso x y ⦋m⦌).symm).isQCatEquivalence

end SerrePositivity.InfinityCategories
