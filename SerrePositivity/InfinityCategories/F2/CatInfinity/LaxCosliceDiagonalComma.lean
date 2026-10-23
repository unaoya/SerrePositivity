module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.FatCoconeHomotopyNaturality
public import SerrePositivity.InfinityCategories.Stable.LaxCosliceNaturality
public import SerrePositivity.InfinityCategories.F1B.UnitCommaFiberExtension

/-!
概要：太い coslice の族と対角関手の固定始域 comma の族を自然に比較する。
方針：太い余錐の普遍性、円柱と自然変換の全単射、comma の普遍性を合成する。
規約：図式・頂点族・実際の自然変換を保持する。
使われ方：対角関手の cofinality を filtered な coslice の弱可縮性へ帰着する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：太い coslice と対角 comma の任意の族の全単射。
方針：固定図式の太い余錐と自然変換のデータを中間に使う。
規約：充填性の仮定なし。使われ方：単体集合の同型の構成。 -/
def laxCosliceDiagonalCommaHomEquiv {K C : SSet.{u}} (p : K ⟶ C) (A : SSet.{u}) :
    (A ⟶ laxCoslice p) ≃ (A ⟶ unitCommaFiber (constantDiagram K C) (functorVertex p)) :=
  (laxCosliceHomEquiv p A).trans ((fatCoconeHomotopyEquiv p A).trans
    (unitCommaFiberFamilyEquiv (constantDiagram K C) (functorVertex p) A).symm)

/-- 概要：太い coslice の族の比較は元の余錐の頂点を保つ。
方針：comma の持ち上げの標的公式を使う。
規約：頂点族は非定値でよい。使われ方：射影を保つ同型の確認。 -/
lemma laxCosliceDiagonalCommaHomEquiv_target {A K C : SSet.{u}} {p : K ⟶ C}
    (f : A ⟶ laxCoslice p) :
    unitCommaFiberTarget (laxCosliceDiagonalCommaHomEquiv p A f) =
      fatJoinInr K A ≫ laxCosliceUncurry f :=
  unitCommaFiberCurry_target _ _ _ _

/-- 概要：太い coslice の族の比較は元の余錐の円柱を保つ。
方針：comma の持ち上げの自然変換公式を使う。
規約：ホモトピー類への移行を行わない。使われ方：比較の自然性の検証。 -/
lemma laxCosliceDiagonalCommaHomEquiv_homotopy {A K C : SSet.{u}} {p : K ⟶ C}
    (f : A ⟶ laxCoslice p) :
    (unitCommaFiberHomotopy (laxCosliceDiagonalCommaHomEquiv p A f)).h =
      (fatCoconeHomotopy (laxCosliceUncurry f) (laxCosliceUncurry_fixed f)).h :=
  unitCommaFiberCurry_homotopy _ _ _ _

/-- 概要：太い coslice と対角 comma の族の比較はパラメータの前合成に自然。
方針：標的族と円柱をそれぞれ前合成の公式で比較する。
規約：全ての単体集合パラメータを同時に扱う。使われ方：Yoneda による同型。 -/
lemma laxCosliceDiagonalCommaHomEquiv_naturality {A B K C : SSet.{u}} {p : K ⟶ C}
    (i : B ⟶ A) (f : A ⟶ laxCoslice p) :
    laxCosliceDiagonalCommaHomEquiv p B (i ≫ f) =
      i ≫ laxCosliceDiagonalCommaHomEquiv p A f := by
  apply unitCommaFiber_hom_ext
  · rw [laxCosliceDiagonalCommaHomEquiv_target, unitCommaFiberTarget_precomp,
      laxCosliceDiagonalCommaHomEquiv_target, laxCosliceUncurry_precomp]
    rw [← Category.assoc, fatJoinInr_map, Category.assoc]
  · rw [laxCosliceDiagonalCommaHomEquiv_homotopy, unitCommaFiberHomotopy_precomp,
      laxCosliceDiagonalCommaHomEquiv_homotopy]
    have h := fatCoconeHomotopy_precomp_h (laxCosliceUncurry f)
      (laxCosliceUncurry_fixed f) i
    simpa only [fatCoconeHomotopy, laxCosliceUncurry_precomp] using! h (by
      rw [← laxCosliceUncurry_precomp]
      exact laxCosliceUncurry_fixed (i ≫ f))

end SerrePositivity.InfinityCategories.F2
