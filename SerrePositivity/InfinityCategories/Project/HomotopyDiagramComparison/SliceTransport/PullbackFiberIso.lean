module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.FibrationAllFibers
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationBoundary

/-!
概要：引き戻し射影の fiber と元の射の fiber の標準同型。
方針：二つの引き戻しの普遍性で互いに逆の射を作る。
規約：底の指定頂点の等式を明示し、Kan 性や fibration 性は使わない。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2、Sp の引き戻しの Ω 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

variable {P E X B : SSet.{u}} {i : P ⟶ E} {j : P ⟶ X} {p : E ⟶ B} {q : X ⟶ B}

/-- 概要：引き戻し射影の fiber を元の射の fiber へ送る。
方針：第一射影と fiber 包含を合成して持ち上げる。
規約：q(x)=b を明示し、底の頂点の表示に依存しない。
使われ方：引き戻しの fiber の標準同型の順射。 -/
def pullbackFiberToOriginal (hP : IsPullback i j p q) (x : X _⦋0⦌) (b : B _⦋0⦌)
    (hxb : q.app _ x = b) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber j x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p b (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι j x ≫ i) (by
    rw [Category.assoc, hP.w, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp, const_comp, hxb])

/-- 概要：元の射の fiber を引き戻し射影の fiber へ戻す。
方針：元の fiber 包含と x の定数写像を引き戻してから fiber へ持ち上げる。
規約：二つの引き戻しの標準の持ち上げを使う。
使われ方：引き戻しの fiber の標準同型の逆射。 -/
def originalFiberToPullback (hP : IsPullback i j p q) (x : X _⦋0⦌) (b : B _⦋0⦌)
    (hxb : q.app _ x = b) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber j x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift j x (hP.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b) (SSet.const x) (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp, const_comp, hxb])) (hP.lift_snd _ _ _)

/-- 概要：順射は元の全空間への包含と第一射影に関して可換。
方針：fiber への持ち上げの第一成分を計算する。
規約：任意の引き戻し正方形に対する射の等式。
使われ方：fiber 間の比較射の自然性。 -/
lemma pullbackFiberToOriginal_ι (hP : IsPullback i j p q) (x : X _⦋0⦌) (b : B _⦋0⦌)
    (hxb : q.app _ x = b) :
    pullbackFiberToOriginal hP x b hxb ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι j x ≫ i := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι ..

/-- 概要：逆射を引き戻しの全空間へ含めると標準の持ち上げとなる。
方針：fiber への持ち上げの第一成分を計算する。
規約：証明項の選択は射を変えない。
使われ方：二つの比較射が逆であることの検証。 -/
lemma originalFiberToPullback_ι (hP : IsPullback i j p q) (x : X _⦋0⦌) (b : B _⦋0⦌)
    (hxb : q.app _ x = b) :
    originalFiberToPullback hP x b hxb ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι j x =
      hP.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b) (SSet.const x) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp, const_comp, hxb]) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι ..

/-- 概要：引き戻し射影の fiber と元の射の指定頂点上の fiber は標準同型。
方針：二つの比較射の合成を fiber の包含後および両射影で検査する。
規約：空の fiber も許し、非空性や Kan 性を仮定しない。
使われ方：Sp の引き戻しの全基点 π_* 比較と零次数の成分の比較。 -/
def pullbackFiberIso (hP : IsPullback i j p q) (x : X _⦋0⦌) (b : B _⦋0⦌)
    (hxb : q.app _ x = b) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber j x ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b where
  hom := pullbackFiberToOriginal hP x b hxb
  inv := originalFiberToPullback hP x b hxb
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext j x
    apply hP.hom_ext
    · simp only [Category.assoc, originalFiberToPullback_ι, hP.lift_fst,
        pullbackFiberToOriginal_ι, Category.id_comp]
    · simp only [Category.assoc, originalFiberToPullback_ι, hP.lift_snd,
        comp_const, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp]
  inv_hom_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p b
    rw [Category.assoc, pullbackFiberToOriginal_ι, ← Category.assoc,
      originalFiberToPullback_ι, hP.lift_fst, Category.id_comp]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
