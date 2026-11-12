module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FiberProjection

/-! # Hom-fiber 座標と標準の脚の合成

概要：fiber の Hom 座標は標準射影と標準ホモトピーへの後合成に一致する。
方針：シフト恒等 cochain の値と rightUnshift の合成式、結合律を使う。
規約：HTT §1.2.13、N7.1。使われ方：slice で得る六式と Hom-fiber の比較の一致。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded CochainComplex HomComplex

variable {A : Type u} [CommRing A] {X B D : Complex A}

/-- 概要：シフト恒等閉元の値は恒等射の cochain の右シフト戻し。
方針：閉元とシフトへの射の同値の定義を評価する。
規約：HTT §1.2.13。使われ方：Hom 座標と標準射影の比較。 -/
lemma fiberShiftCocycle_val (f : B ⟶ D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberShiftCocycle f).val =
      (Cochain.ofHom (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiber f))).rightUnshift (-1) (zero_add (-1)) := rfl

/-- 概要：fiber への Hom のシフト戻しはシフト恒等閉元との合成。
方針：恒等射との合成へ rightUnshift_comp を適用する。
規約：HTT §1.2.13。使われ方：全次数の座標が標準の脚を使うことの検証。 -/
lemma fiberUnshift_eq_comp (f : B ⟶ D) (n : ℤ) (a : Cochain X (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiber f) (n + 1)) :
    a.rightUnshift n (by omega) = a.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberShiftCocycle f).val (by omega) := by
  have h := Cochain.rightUnshift_comp a (Cochain.ofHom (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiber f)))
    (add_zero (n + 1)) n (by omega) (-1) (zero_add (-1))
  simpa only [Cochain.comp_id, fiberShiftCocycle_val] using h

/-- 概要：fiber Hom の第一座標は標準射影との後合成。
方針：シフト戻しをシフト恒等 cochain との合成へ直して結合律を使う。
規約：HTT §1.2.13、N7.1。使われ方：錐の脚から作る Hom 比較との一致。 -/
lemma fiberHomCoordinates_fst_eq_comp (f : B ⟶ D) (n : ℤ)
    (a : Cochain X (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiber f) (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberHomCoordinates f n a).1 =
      a.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberProjection f)) (add_zero (n + 1)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberHomCoordinates_fst, fiberUnshift_eq_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberProjection_cochain]
  exact Cochain.comp_assoc _ _ _ (by omega) (by omega) (by omega)

/-- 概要：fiber Hom の第二座標は標準ホモトピーとの後合成。
方針：シフト戻しの合成式と零次数の snd を含む結合律を使う。
規約：HTT §1.2.13、N7.1。使われ方：錐の高次成分から作る Hom 比較との一致。 -/
lemma fiberHomCoordinates_snd_eq_comp (f : B ⟶ D) (n : ℤ)
    (a : Cochain X (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiber f) (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberHomCoordinates f n a).2 = a.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberNullHomotopy f) (by omega) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberHomCoordinates_snd, fiberUnshift_eq_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberNullHomotopy, Cochain.comp_neg]
  congr 1
  exact Cochain.comp_assoc_of_third_is_zero_cochain _ _ _ (by omega)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
