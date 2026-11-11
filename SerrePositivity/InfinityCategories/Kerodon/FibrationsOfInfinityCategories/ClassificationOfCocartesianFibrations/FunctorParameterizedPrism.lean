module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexPrismFirstVertex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorFamilyPrism

/-!
概要：追加パラメーターを持つ関手空間の族を単体の prism の評価へ移す。
方針：対称子と結合子で因子を並べ替え、uncurry で評価する。
規約：単体のパラメーターと追加パラメーターを別々に保持する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な変換の空間全体の評価。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：追加パラメーターを持つ関手空間への族を、パラメーター付きの prism の評価にする。
方針：因子を B、K、L の順へ並べ替えてから uncurry する。
規約：K、B、L は任意の単体集合。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、変換の空間全体を評価する族。 -/
def functorParameterizedPrism {K B L X : SSet.{u}}
    (H : K ⊗ L ⟶ (ihom B).obj X) : (K ⊗ B) ⊗ L ⟶ X :=
  ((β_ K B).hom ▷ L) ≫ (α_ B K L).hom ≫ uncurry H

/-- 概要：単体の指定頂点での因子の交換は、追加パラメーターの指定頂点への包含と一致する。
方針：各次数の直積の三成分を計算する。
規約：頂点の番号 i を固定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、変換の族の端点での評価。 -/
lemma simplexPrismVertex_exchange (n : ℕ) (i : Fin (n + 1)) (B L : SSet.{u}) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n i B ▷ L) ≫ ((β_ (Δ[n] : SSet.{u}) B).hom ▷ L)) ≫
      (α_ B (Δ[n] : SSet.{u}) L).hom = B ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n i L := rfl

/-- 概要：追加パラメーター付きの prism を指定頂点で制限すると、元の関手空間の族のその頂点での評価になる。
方針：頂点包含の交換の計算と uncurry の自然性を使う。
規約：次元 n と追加パラメーター L は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な変換の族の始点・終点の固定。 -/
lemma functorParameterizedPrism_vertex {B L X : SSet.{u}} (n : ℕ)
    (H : (Δ[n] : SSet.{u}) ⊗ L ⟶ (ihom B).obj X) (i : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n i B ▷ L) ≫ functorParameterizedPrism H =
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n i L ≫ H) := by
  rw [functorParameterizedPrism, ← Category.assoc, ← Category.assoc,
    simplexPrismVertex_exchange, ← uncurry_natural_left]

/-- 概要：頂点で指定した関手に定値な関手空間の族の評価は、元の定義域への射影の後の関手になる。
方針：頂点への制限と定値の関手頂点の uncurry を計算する。
規約：定値性は追加パラメーター全体での等式として仮定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、変換の空間全体の評価の固定端点。 -/
lemma functorParameterizedPrism_vertex_of_const {B L X : SSet.{u}} (n : ℕ)
    (H : (Δ[n] : SSet.{u}) ⊗ L ⟶ (ihom B).obj X) (i : Fin (n + 1))
    (F : B ⟶ X) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n i L ≫ H = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n i B ▷ L) ≫ functorParameterizedPrism H = fst B L ≫ F := by
  rw [functorParameterizedPrism_vertex, hi, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 概要：単体の prism の指定頂点への制限は、底の図式の定義域の引き戻しと可換。
方針：テンソルの射の合成則と頂点包含の自然性を使う。
規約：追加パラメーター L を固定したまま計算する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、普遍的な変換の持ち上げの終点の底の計算。 -/
lemma simplexPrismVertex_parameterizedBaseChange {A B L X : SSet.{u}}
    (n : ℕ) (i : Fin (n + 1)) (p : A ⟶ B) (T : ((Δ[n] : SSet.{u}) ⊗ B) ⊗ L ⟶ X) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n i A ▷ L) ≫ ((Δ[n] ◁ p) ▷ L)) ≫ T =
      (p ▷ L) ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n i B ▷ L) ≫ T) := by
  rw [← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex_naturality, comp_whiskerRight, Category.assoc]

/-- 概要：零単体の因子を含む初期制限の条件から、追加パラメーター全体の最初の値の等式を回収する。
方針：零単体の因子への射影の切断で前合成して、同じ因子を消去する。
規約：最初の値 f は追加パラメーターに関して定値。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、普遍的な持ち上げの族の始点の計算。 -/
lemma simplexPrism_initialRestriction {A L X : SSet.{u}} (n : ℕ)
    (W : ((Δ[n] : SSet.{u}) ⊗ A) ⊗ L ⟶ X) (f : A ⟶ X)
    (h : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n ▷ A) ▷ L) ≫ W =
      fst (Δ[0] ⊗ A) L ≫ snd (Δ[0] : SSet.{u}) A ≫ f) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n 0 A ▷ L) ≫ W = fst A L ≫ f := by
  let r := snd (Δ[0] : SSet.{u}) A ▷ L
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex 0 0 A ▷ L
  have hs : s ≫ r = 𝟙 (A ⊗ L) := by
    rw [← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex_snd, id_whiskerRight]
  have h' : r ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex n 0 A ▷ L) ≫ W) = r ≫ (fst A L ≫ f) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, comp_whiskerRight, Category.assoc,
      whiskerRight_fst_assoc, r] using h
  have hh := congrArg (fun k => s ≫ k) h'
  simpa only [← Category.assoc, hs, Category.id_comp] using hh

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
