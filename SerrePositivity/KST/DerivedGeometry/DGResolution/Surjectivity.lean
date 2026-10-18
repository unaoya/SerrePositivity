module

public import SerrePositivity.KST.DerivedGeometry.DGResolution.Construction

/-!
# 増大関手の各次数の全射性

概要：Lemma 13.5 の増大関手が斉次元の上でも全射であることを証明する。
方針：斉次元の微分を初期の閉元被覆へ持ち上げ、最初の境界添加で原始元を得る。
規約：Hom の準同型性だけから次数ごとの全射性を結論しない。
使われ方：Drinfeld Lemma 13.5、KST D4 と一般の Verdier 商の分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

namespace SerrePositivity.KST.DerivedGeometry.DGResolution

open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/--
概要：最初の境界生成元添加の増大射は各次数で全射。
方針：与えられた元の微分を閉元として持ち上げ、その原始元を添加する。
規約：初期の閉元被覆自体の次数全射性は要求しない。
使われ方：Drinfeld Lemma 13.5 の全射条件。
-/
theorem firstStage_surjective (x y : D) (n : ℤ) :
    Function.Surjective ((DGCategoryCellResolution.stageAugmentation A D 1 x y).f n) := by
  intro b
  let K := homObject A D x y
  let z : complexCycles A K (n + 1) := ⟨K.d n (n + 1) b, by
    change K.d (n + 1) (n + 1 + 1) (K.d n (n + 1) b) = 0
    exact congrArg (fun f => f b) (K.d_comp_d n (n + 1) (n + 1 + 1))⟩
  obtain ⟨t, ht⟩ := DGCategoryCycleCover.cycle_lift A D x y (n + 1) z
  let c : ComplexBoundaryCell A (DGCategoryCellResolution.stageAugmentation A D 0 x y) :=
    ⟨n, t, b, ht.symm⟩
  obtain ⟨a, _, ha⟩ := DGCategoryCellResolution.stage_fills A D 0 x y c
  exact ⟨a, ha⟩

/--
概要：極限の増大射は各次数で全射。
方針：最初の境界添加で得た原始元を逐次余極限へ送る。
規約：余極限の構成は既存の具体的な Hom 列。
使われ方：Drinfeld Lemma 13.5 の全射準同型。
-/
theorem augmentation_surjective (x y : Objects A D) (n : ℤ) :
    Function.Surjective (((augmentation A D).map x y).f n) := by
  intro b
  obtain ⟨a, ha⟩ := firstStage_surjective A D x.val y.val n b
  refine ⟨(DGCategoryCellResolution.stageInclusion A D 1 x.val y.val).f n a, ?_⟩
  have h := congrArg (fun f => f.f n a)
    (DGCategoryCellResolution.stageInclusion_augmentation A D 1 x.val y.val)
  exact h.trans ha

/--
概要：増大関手の各 Hom の各次数は加群圏の全射。
方針：斉次元の全射性を加群圏の Epi へ変換する。
規約：分解・平坦性の存在を引数に取らない。
使われ方：Drinfeld Lemma 13.5 の分解と持ち上げの入口。
-/
instance augmentation_degree_epi (x y : Objects A D) (n : ℤ) :
    Epi (((augmentation A D).map x y).f n) :=
  (ModuleCat.epi_iff_surjective _).mpr (augmentation_surjective A D x y n)

end SerrePositivity.KST.DerivedGeometry.DGResolution
