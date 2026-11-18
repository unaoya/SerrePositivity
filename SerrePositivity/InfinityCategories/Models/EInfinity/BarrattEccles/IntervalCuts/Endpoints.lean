module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GeneratorLinearExt
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainCounitValues

/-!
模型。文献の定義との比較は後で
# 正規化区間の端点と収縮の実際の複体射

概要：Berger–Fresse §3.1・Berger–Moerdijk 命題 4.1 の区間の底の三角形を構成する。
方針：端点頂点の閉元から sphere 射を作り、AW 余単位を収縮として用いる。
規約：端点 false は零、true は一、底は実際の正規化 Δ¹。
使われ方：E-coalgebra 区間の端点・収縮の余作用保存と区間条件。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：区間端点を表す零次の閉元（BF §3.1）。
方針：実際の頂点生成元を取り、正整数成分の零性で閉性を確認する。
規約：false を零頂点、true を一頂点とする。
使われ方：単位複体からの端点射。 -/
def endpointCycle (b : Bool) : complexCycles A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) 0 :=
  ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex (if b then 1 else 0)),
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval_eq_zero_of_other A 1 (by decide) (by decide) _⟩

/-- 概要：正規化区間の端点を与える実際の複体射（BF §3.1）。
方針：端点閉元を単一成分複体の普遍性で射へ移す。
規約：始域は整数複体のテンソル単位。
使われ方：具体的な E-coalgebra 区間の endpoint フィールド。 -/
def endpoint (b : Bool) : 𝟙_ (Complex A) ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A :=
  complexSphereMap A 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointCycle A b)

/-- 概要：端点射の零次は頂点生成元のスカラー倍（BF §3.1）。
方針：sphere 射の零次公式と元に対応する加群射を評価する。
規約：単位の零次元を singleObjXSelf の逆で指定する。
使われ方：端点の余作用保存を生成元で比較する。 -/
lemma endpoint_zero_apply (b : Bool) (a : A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv a) =
      a • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex (if b then 1 else 0)) := by
  have h : (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b).f 0 =
      moduleElementMap A ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpointCycle A b).val := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint, complexSphereMap]
    rw [mkHomFromSingle_f, Iso.inv_hom_id_assoc]
  exact congrArg (fun f => f a) h

/-- 概要：正規化区間から単位への収縮は AW の余単位（BF §3.1）。
方針：一般の正規化コチェイン余単位を Δ¹ に適用する。
規約：単なる複体射として定義し、余作用保存は後に証明する。
使われ方：具体的な区間の contraction フィールド。 -/
def contraction : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A ⟶ 𝟙_ (Complex A) :=
  _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A Δ[1]

/-- 概要：収縮は両頂点生成元を単位に送る（BF §3.1）。
方針：面生成元と標準頂点を同定し、AW 余単位の生成元値を使う。
規約：出力の零次は singleObjXSelf で A と比較する。
使われ方：端点・収縮の三角形と余作用保存。 -/
lemma contraction_vertex (b : Fin 2) :
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction A).f 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b))) = (1 : A) := by
  refine (congrArg (fun x => (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction A).f 0 x)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector_vertex_eq A b)).trans ?_
  exact _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_generator_zero A Δ[1] (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexSimplex b)

/-- 概要：両端点の後の収縮は単位複体の恒等射（BM 命題 4.1、BF §3.1）。
方針：single 複体からの射を零次で比較し、単位の生成元の像を計算する。
規約：false・true の双方で同じ収縮を使う。
使われ方：具体的な区間の endpoint_contraction フィールド。 -/
lemma endpoint_contraction (b : Bool) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction A = 𝟙 _ := by
  apply from_single_hom_ext
  apply (cancel_epi (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv).mp
  apply (cancel_mono (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction A).f 0 ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint A b).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)))) = (1 : A)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint_zero_apply, one_smul]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.contraction_vertex A _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
