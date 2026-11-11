module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorExtensionEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPrecomposition

/-!
概要：底と初期値を固定した相対延長の始域制限は元の初期値を保つ。
方針：二つの制限の可換正方形と内部 Hom の前合成則を使う。
規約：全パラメータでの等式。使われ方：全空間の比較同型を各点の比較へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の延長族を可換正方形で制限すると制限した初期値に厳密に一致する。
方針：固定された初期値の式と内部 Hom の前合成の関手性。
規約：単射・充填性の仮定なし。使われ方：相対延長空間の制限写像の構成。 -/
lemma relativeExtensionRestriction_condition {A D A' D' E B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E)
    (hv : v ≫ p = i ≫ b) (h : A' ⟶ A) (k : D' ⟶ D) (i' : D' ⟶ A')
    (hs : i' ≫ h = k ≫ i) :
    relativeFunctorExtensionSpaceι p b i v hv ≫
        vertexFiberι ((ihom A).map p) (functorVertex b) ≫
          (pre h).app E ≫ (pre i').app E = SSet.const (functorVertex (k ≫ v)) := by
  have h₀ : relativeFunctorExtensionSpaceι p b i v hv ≫
      vertexFiberι ((ihom A).map p) (functorVertex b) ≫ (pre i).app E =
        SSet.const (functorVertex v) := by
    have e := congrArg (fun z => z ≫ vertexFiberι ((ihom D).map p)
      (functorVertex (i ≫ b))) (relativeFunctorExtensionSpaceι_pre p b i v hv)
    simp only [Category.assoc, relativeFunctorPre_ι, SSet.const_comp] at e
    change relativeFunctorExtensionSpaceι p b i v hv ≫
      vertexFiberι ((ihom A).map p) (functorVertex b) ≫ (pre i).app E =
        SSet.const (functorVertex v) at e
    exact e
  have hp : (pre h).app E ≫ (pre i').app E = (pre i).app E ≫ (pre k).app E := by
    rw [← NatTrans.comp_app, ← pre_map, hs, pre_map, NatTrans.comp_app]
  calc
    _ = relativeFunctorExtensionSpaceι p b i v hv ≫
        vertexFiberι ((ihom A).map p) (functorVertex b) ≫ (pre i).app E ≫ (pre k).app E :=
      congrArg (fun z : (ihom A).obj E ⟶ (ihom D').obj E =>
        relativeFunctorExtensionSpaceι p b i v hv ≫
          vertexFiberι ((ihom A).map p) (functorVertex b) ≫ z) hp
    _ = SSet.const (functorVertex v) ≫ (pre k).app E := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ (pre k).app E) h₀
    _ = SSet.const (functorVertex (k ≫ v)) := by
      rw [SSet.const_comp]
      rfl

end SerrePositivity.InfinityCategories.F2
