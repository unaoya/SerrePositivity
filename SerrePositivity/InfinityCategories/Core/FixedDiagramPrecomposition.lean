module

public import SerrePositivity.InfinityCategories.Core.PrecompositionFiberEquivalence
public import SerrePositivity.InfinityCategories.Core.PrecompositionMonomorphism

/-!
概要：図式を固定した内部 Hom の前合成。
方針：前合成の可換正方形を頂点の fiber へ制限する。
規約：共通の部分の図式は厳密に固定する。
使われ方：Kerodon §4.6.4 の圏論的円柱の両端。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：共通部分を保つ前合成は固定図式上の関手圏を写す。
方針：前合成の合成則で可換性を確認して fiber の誘導射を作る。
規約：単射性や quasicategory 性は不要。
使われ方：Kerodon §4.6.4 の円柱の射の制限。 -/
def fixedDiagramPre {K T U X : SSet.{u}} (j : K ⟶ T) (k : K ⟶ U)
    (q : U ⟶ T) (h : k ≫ q = j) (p : K ⟶ X) :
    vertexFiber ((pre j).app X) (functorVertex p) ⟶
      vertexFiber ((pre k).app X) (functorVertex p) :=
  vertexFiberMap _ _ ((pre q).app X)
    (by rw [← NatTrans.comp_app, ← pre_map, h]) (functorVertex p)

/-- 概要：固定図式上の前合成は合成と整合する。
方針：fiber の包含後に前合成の合成則を計算する。
規約：等式の証明の選択は問わない。
使われ方：Kerodon §4.6.4 の円柱と両端の射影。 -/
lemma fixedDiagramPre_comp {K T U V X : SSet.{u}}
    (j : K ⟶ T) (k : K ⟶ U) (l : K ⟶ V)
    (q : U ⟶ T) (r : V ⟶ U) (hq : k ≫ q = j) (hr : l ≫ r = k) (p : K ⟶ X) :
    fixedDiagramPre j k q hq p ≫ fixedDiagramPre k l r hr p =
      fixedDiagramPre j l (r ≫ q) (by rw [← Category.assoc, hr, hq]) p := by
  apply vertexFiber_hom_ext ((pre l).app X) (functorVertex p)
  simp only [fixedDiagramPre, Category.assoc, vertexFiberMap_ι]
  rw [← Category.assoc, vertexFiberMap_ι]
  simp only [pre_map, NatTrans.comp_app, Category.assoc]

/-- 概要：恒等による固定図式上の前合成は恒等。
方針：fiber の誘導射の恒等則。
規約：共通部分の包含は任意。
使われ方：Kerodon §4.6.4 の円柱の厳密な切断。 -/
lemma fixedDiagramPre_id {K T X : SSet.{u}} (j : K ⟶ T) (p : K ⟶ X) :
    fixedDiagramPre j j (𝟙 T) (by simp) p = 𝟙 _ := by
  apply vertexFiber_hom_ext ((pre j).app X) (functorVertex p)
  simp only [fixedDiagramPre, vertexFiberMap_ι, pre_id, NatTrans.id_app,
    Category.comp_id, Category.id_comp]

/-- 概要：エピな普遍的同値による前合成は固定図式上でも同値。
方針：前合成は単射な同値なので fiber の比較補題を適用する。
規約：共通部分の二包含は単射、X は quasicategory。
使われ方：Kerodon §4.6.4 の可逆円柱の射影。 -/
lemma isQCatEquivalence_fixedDiagramPre {K T U X : SSet.{u}} [Quasicategory X]
    (j : K ⟶ T) (k : K ⟶ U) [Mono j] [Mono k]
    (q : U ⟶ T) [Epi q] (h : k ≫ q = j) (p : K ⟶ X)
    (hq : IsPrecompositionEquivalence q) : IsQCatEquivalence (fixedDiagramPre j k q h p) := by
  apply isQCatEquivalence_vertexFiberMap_pre
  exact hq X

end SerrePositivity.InfinityCategories
