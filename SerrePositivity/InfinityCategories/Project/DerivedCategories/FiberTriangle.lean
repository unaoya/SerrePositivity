module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Homology
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-! # 標準 fiber の distinguished triangle

概要：N7 の標準 fiber の射影は Mathlib の mapping cocone の射影と一致する。
方針：Hom のシフト規約を成分で照合し、既存の distinguished triangle を適用する。
規約：射影の符号を保持する。使われ方：D6a の指定された四辺の長完全列。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable {S : Type u} [CommRing S] {B D : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 概要：標準 fiber の射影は Mathlib の mapping cocone の第一射である。
方針：右シフトから戻した恒等 cochain と左シフトの Koszul 符号を計算する。
規約：同じ mapping cone の −1 シフトを使う。使われ方：標準 fiber の三角形への接続。 -/
lemma fiberProjection_eq_mappingCocone_fst (f : B ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberProjection f = mappingCocone.fst f := by
  apply HomologicalComplex.hom_ext
  intro p
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberProjectionCycle f).val.v p p (add_zero p) = _
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberProjectionCycle, Cocycle.mk]
  rw [Cochain.comp_v _ _ _ p (p - 1) p (by omega) (by omega)]
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberShiftCocycle, Cocycle.equivHomShift_apply, Cochain.rightUnshift_v,
    mappingCocone.fst, Cocycle.leftShift, Cochain.leftShift, Cochain.mk_v, Cocycle.homOf_f,
    Cochain.ofHom_v, sub_eq_add_neg]
  congr 1

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]
open Pretriangulated

/-- 概要：標準 fiber → B → D の導来圏の三角形。
方針：mapping cocone の三角形を局所化関手で送る。
規約：第一射は N7 の fiber 射影、第二射は f。使われ方：長完全列の出発点。 -/
def standardFiberDerivedTriangle (f : B ⟶ D) : Triangle (DerivedCategory (ModuleCat S)) :=
  DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle f)

/-- 概要：標準 fiber の三角形は distinguished である。
方針：Mathlib の mapping cocone の distinguished 性を用いる。
規約：D3 と同じ導来圏とシフト。使われ方：各次数の長完全列。 -/
lemma standardFiberDerivedTriangle_distinguished (f : B ⟶ D) :
    standardFiberDerivedTriangle f ∈ distTriang (DerivedCategory (ModuleCat S)) :=
  DerivedCategory.mappingCocone_triangle_distinguished f

/-- 概要：標準 fiber の三角形の第一射は N7 の指定した射影の像である。
方針：射影の符号比較を適用する。
規約：射影の負号の変更はない。使われ方：指定脚との整合。 -/
lemma standardFiberDerivedTriangle_mor₁ (f : B ⟶ D) :
    (standardFiberDerivedTriangle f).mor₁ = DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberProjection f) := by
  change DerivedCategory.Q.map (mappingCocone.fst f) = _
  rw [fiberProjection_eq_mappingCocone_fst]

/-- 概要：標準 fiber の三角形の第二射は元の f の像である。
方針：定義を評価する。
規約：差の射の場合も符号を保持する。使われ方：右辺 − 下辺の固定。 -/
lemma standardFiberDerivedTriangle_mor₂ (f : B ⟶ D) :
    (standardFiberDerivedTriangle f).mor₂ = DerivedCategory.Q.map f := rfl

variable {A : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 概要：標準 fiber に擬同型な A を第一頂点とする三角形。
方針：比較射の局所化像の逆をシフトし、接続射の終域を A[1] に移す。
規約：第一射は比較射と fiber 射影の合成。使われ方：引き戻し四角形の頂点への移送。 -/
def fiberComparisonDerivedTriangle (f : B ⟶ D) (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiber f) [QuasiIso a] :
    Triangle (DerivedCategory (ModuleCat S)) :=
  Triangle.mk (DerivedCategory.Q.map (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberProjection f)) (DerivedCategory.Q.map f)
    ((standardFiberDerivedTriangle f).mor₃ ≫ inv ((DerivedCategory.Q.map a)⟦(1 : ℤ)⟧'))

/-- 概要：比較三角形と標準 fiber 三角形は比較射で同型になる。
方針：第一頂点に擬同型の像の同型を置き、他の二頂点には恒等同型を置く。
規約：三つの射の可換性を含む。使われ方：distinguished 性の移送。 -/
def fiberComparisonDerivedTriangleIso (f : B ⟶ D) (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiber f) [QuasiIso a] :
    fiberComparisonDerivedTriangle f a ≅ standardFiberDerivedTriangle f := by
  refine Triangle.isoMk _ _ (asIso (DerivedCategory.Q.map a)) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_
  · change DerivedCategory.Q.map (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberProjection f) ≫ 𝟙 _ =
      DerivedCategory.Q.map a ≫ (standardFiberDerivedTriangle f).mor₁
    rw [Category.comp_id, standardFiberDerivedTriangle_mor₁, Functor.map_comp]
  · simp [fiberComparisonDerivedTriangle, standardFiberDerivedTriangle]
  · change ((standardFiberDerivedTriangle f).mor₃ ≫ inv ((DerivedCategory.Q.map a)⟦(1 : ℤ)⟧')) ≫
      (DerivedCategory.Q.map a)⟦(1 : ℤ)⟧' = 𝟙 _ ≫ (standardFiberDerivedTriangle f).mor₃
    simp

/-- 概要：標準 fiber に擬同型な頂点への比較三角形は distinguished である。
方針：標準三角形との同型により distinguished 性を移す。
規約：擬同型以外の追加条件なし。使われ方：引き戻しの長完全列。 -/
lemma fiberComparisonDerivedTriangle_distinguished (f : B ⟶ D)
    (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiber f) [QuasiIso a] :
    fiberComparisonDerivedTriangle f a ∈ distTriang (DerivedCategory (ModuleCat S)) :=
  isomorphic_distinguished _ (standardFiberDerivedTriangle_distinguished f) _
    (fiberComparisonDerivedTriangleIso f a)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
