module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Anodyne.KanTwoHornLift
public import SerrePositivity.HomotopicalAlgebra.Simplicial.CurriedHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses

/-!
# Kan値の写像のホモトピー類が等しいことと実際の区間ホモトピーの存在が同値となる

## 概要
Kan値の写像のホモトピー類が等しいことと実際の区間ホモトピーの存在が同値となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
テンソルと内部Homの随伴で族を転置し、対応する境界の等式を比較する。
転置の単射性と自然性により、元の全パラメータ族の等式へ戻す。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0406][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0406
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual homotopies representing equality of Kan-valued homotopy classes

An outer two-horn in the mapping space supplies right differences of
homotopies. Hence actual homotopies are symmetric and transitive for Kan
targets, and every equality in the generated quotient has a single interval.
No model structure is assumed on the value universe.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.SimplicialModel.KanActualHomotopy

private lemma vertex_zero :
    SSet.stdSimplex.δ.{v} (1 : Fin 2) ≫ SSet.stdSimplex.δ (2 : Fin 3) =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (1 : Fin 3) := by
  change SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
    SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) =
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
        SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 3))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg SSet.stdSimplex.map (by decide)

private lemma vertex_one :
    SSet.stdSimplex.δ.{v} (0 : Fin 2) ≫ SSet.stdSimplex.δ (2 : Fin 3) =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (0 : Fin 3) := by
  change SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫
    SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) =
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) ≫
        SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 3))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg SSet.stdSimplex.map (by decide)

variable {X K : SSet.{v}} (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
  {f g h : X ⟶ K}

def refl (f : X ⟶ K) : SSet.Homotopy f f :=
  SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm f)

include hK in
lemma right_difference (Hfg : SSet.Homotopy f g) (Hhg : SSet.Homotopy h g) :
    Nonempty (SSet.Homotopy f h) := by
  have : Fibration (terminal.from K) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mpr hK
  have : SSet.KanComplex K := (isFibrant_iff K).mpr inferInstance
  have hp : SSet.modelCategoryQuillen.J.rlp (terminal.from ((ihom X).obj K)) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  have hc : SSet.stdSimplex.δ (0 : Fin 2) ≫ curry Hhg.h =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ curry Hfg.h :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_one Hhg).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_one Hfg).symm
  obtain ⟨t, ht₀, ht₁, _⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exists_triangle _ hp
    (curry Hhg.h) (curry Hfg.h) (terminal.from _) hc
    (terminal.hom_ext _ _) (terminal.hom_ext _ _)
  have hz : SSet.stdSimplex.δ (1 : Fin 2) ≫ (SSet.stdSimplex.δ (2 : Fin 3) ≫ t) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point f := by
    rw [← Category.assoc, vertex_zero, Category.assoc, ht₁]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_zero Hfg
  have ho : SSet.stdSimplex.δ (0 : Fin 2) ≫ (SSet.stdSimplex.δ (2 : Fin 3) ≫ t) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point h := by
    rw [← Category.assoc, vertex_one, Category.assoc, ht₀]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_zero Hhg
  exact ⟨CurriedHomotopy.ofEdge _ hz ho⟩

include hK in
lemma reverse (H : SSet.Homotopy f g) : Nonempty (SSet.Homotopy g f) :=
  right_difference hK (refl g) H

include hK in
lemma concatenate (Hfg : SSet.Homotopy f g) (Hgh : SSet.Homotopy g h) :
    Nonempty (SSet.Homotopy f h) := by
  obtain ⟨Hhg⟩ := reverse hK Hgh
  exact right_difference hK Hfg Hhg

include hK in
lemma relation_equivalence : Equivalence (fun (f g : X ⟶ K) =>
    Nonempty (SSet.Homotopy f g)) :=
  ⟨fun f => ⟨refl f⟩, fun ⟨H⟩ => reverse hK H,
    fun ⟨Hfg⟩ ⟨Hgh⟩ => concatenate hK Hfg Hgh⟩

include hK in
lemma of_class_eq (heq : HomotopyClasses.mk f = HomotopyClasses.mk g) :
    Nonempty (SSet.Homotopy f g) :=
  (relation_equivalence hK).eqvGen_iff.mp (Quot.eqvGen_exact heq)

include hK in
/-- Kan値の写像のホモトピー類が等しいことと実際の区間ホモトピーの存在が同値となる。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
テンソルと内部Homの随伴で族を転置し、対応する境界の等式を比較する。
転置の単射性と自然性により、元の全パラメータ族の等式へ戻す。
-/
lemma class_eq_iff : HomotopyClasses.mk f = HomotopyClasses.mk g ↔
    Nonempty (SSet.Homotopy f g) :=
  ⟨of_class_eq hK, fun ⟨H⟩ => HomotopyClasses.sound H⟩

end SerrePositivity.SimplicialModel.KanActualHomotopy
