module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FiberHomCoordinates

/-! # 標準 fiber の射影と標準ホモトピー

概要：mapping cone の −1 シフトから元の始域へ射影し、元の射との合成を零ホモトピックにする。
方針：シフト恒等射を閉次数 −1 の cochain として読み、fst・snd の微分式を用いる。
規約：HTT §1.2.13、HA Example 1.3.1.8。使われ方：N7c の引き戻し錐の辺と三角形。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded CochainComplex HomComplex

variable {A : Type u} [CommRing A] {B D : Complex A}

/-- 概要：標準 fiber から cone へのシフト恒等 cochain は閉次数 −1。
方針：fiber の恒等 chain map を Hom とシフトの閉元の同値で読む。
規約：HTT §1.2.13。使われ方：標準射影と標準ホモトピーの共通の始域移送。 -/
def fiberShiftCocycle (f : B ⟶ D) : Cocycle (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiber f) (mappingCone f) (-1) :=
  Cocycle.equivHomShift (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiber f))

/-- 概要：標準 fiber の始域への射影は閉次数零元。
方針：閉次数 −1 のシフト恒等 cochain と閉次数 +1 の fst を合成する。
規約：HTT §1.2.13。使われ方：標準 fiber の射影 chain map。 -/
def fiberProjectionCycle (f : B ⟶ D) : Cocycle (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiber f) B 0 :=
  Cocycle.mk ((fiberShiftCocycle f).val.comp (mappingCone.fst f).val (by omega)) 1 rfl (by
    rw [δ_comp _ _ _ 0 2 1 rfl (by omega) rfl]
    simp only [Cocycle.δ_eq_zero, Cochain.comp_zero, Cochain.zero_comp, smul_zero, add_zero])

/-- 概要：標準 fiber から元の始域への射影 chain map。
方針：閉次数零元を通常の複体の射へ戻す。
規約：HTT §1.2.13。使われ方：二項直和の射影と合わせた引き戻しの二脚。 -/
def fiberProjection (f : B ⟶ D) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiber f ⟶ B := (fiberProjectionCycle f).homOf

/-- 概要：射影 chain map の cochain はシフト恒等 cochain と fst の合成。
方針：閉零元と chain map の同値の逆則を使う。
規約：HTT §1.2.13。使われ方：標準ホモトピーの微分の計算。 -/
lemma fiberProjection_cochain (f : B ⟶ D) :
    Cochain.ofHom (fiberProjection f) =
      (fiberShiftCocycle f).val.comp (mappingCone.fst f).val (by omega) :=
  Cocycle.cochain_ofHom_homOf_eq_coe (fiberProjectionCycle f)

/-- 概要：標準 fiber の射影と元の射の合成を零にする次数 −1 の cochain。
方針：シフト恒等 cochain と snd を合成し負を取る。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：引き戻し錐の標準三角形。 -/
def fiberNullHomotopy (f : B ⟶ D) : Cochain (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiber f) D (-1) :=
  -((fiberShiftCocycle f).val.comp (mappingCone.snd f) (add_zero (-1)))

/-- 概要：標準ホモトピーの微分は射影と元の射の合成。
方針：δ_snd と閉じたシフト恒等 cochain の Leibniz 則を用いる。
規約：HA Example 1.3.1.8、HTT §1.2.13。使われ方：fiber 錐の二単体の方程式。 -/
lemma fiberNullHomotopy_differential (f : B ⟶ D) :
    δ (-1) 0 (fiberNullHomotopy f) = Cochain.ofHom (fiberProjection f ≫ f) := by
  rw [fiberNullHomotopy, δ_neg, δ_comp _ _ _ 0 1 0 (by omega) (by omega) rfl]
  simp only [Cocycle.δ_eq_zero, Int.negOnePow_zero, one_smul, Cochain.zero_comp,
    add_zero, mappingCone.δ_snd, Cochain.comp_neg, neg_neg]
  rw [Cochain.ofHom_comp, fiberProjection_cochain]
  exact (Cochain.comp_assoc _ _ _ (by omega : (-1 : ℤ) + 1 = 0) (add_zero 1) (by omega)).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
