module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathNerve
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HollowCube

/-!
# Path の Hom における空洞部分の充填

概要：内部ホーンから既知となる path の Hom の空洞部分は Kan 複体内で充填できる。
方針：内部点座標の同型で空洞立方体の anodyne 性を移送する。
規約：元のホーンから空洞部分上の写像を作る貼合せは HornHollow で実装する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）・2.4.5.12（Tag 00LV） の充填の Hom 側。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialThickening
  HomotopicalAlgebra

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {J : Type u} [LinearOrder J] {a b : J}

/-- 概要：指定内部点の下面を除く path の Hom の空洞部分を定義する。
方針：path の内部点座標で空洞立方体の逆像を取る。
規約：a<b、i は開区間内。包含規約を用いる。
使われ方：Kerodon 2.4.5.8（Tag 00LR） のホーンの端点 Hom の像に対応する候補部分。 -/
noncomputable def pathHollow (hab : a < b) (i : Set.Ioo a b) :
    (nerve (Path a b)).Subcomplex :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCube i).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathInteriorNerveIso hab).hom

/-- 概要：path の空洞部分への所属を最初と最後の path で特徴付ける。
方針：内部点の座標における空洞立方体の所属判定を移す。
規約：最初に共通の内部点があるか、最後が指定外の内部点を欠くという条件。
使われ方：Kerodon 2.4.5.8（Tag 00LR） の面と合成から既知になるデータの回収。 -/
lemma mem_pathHollow_iff (hab : a < b) (i : Set.Ioo a b)
    {n : SimplexCategoryᵒᵖ} (F : (nerve (Path a b)).obj n) :
    F ∈ (pathHollow hab i).obj n ↔
      (∃ x : Set.Ioo a b, x.1 ∈ (F.obj 0).I) ∨
        ∃ x : Set.Ioo a b, x ≠ i ∧ x.1 ∉ (F.obj (Fin.last n.unop.len)).I := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathInteriorNerveIso hab).hom.app n F) ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCube i).obj n ↔ _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.mem_hollowCube_endpoints_iff i ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathInteriorNerveIso hab).hom.app n F)

/-- 概要：path の空洞部分の包含は anodyne。
方針：内部点座標の同型に沿って空洞立方体の結果を移す。
規約：局所 Kan 性はこの包含の性質には不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.12（Tag 00LV） の Hom 空間の延長。 -/
lemma pathHollow_anodyne (hab : a < b) (i : Set.Ioo a b) :
    SSet.anodyneExtensions (pathHollow hab i).ι :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.anodyne_subcomplexPreimage (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathInteriorNerveIso hab) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hollowCube_anodyne i)

/-- 概要：Kan 複体への path の空洞部分上の写像を全 Hom 単体集合へ延長する。
方針：anodyne 包含と終対象への Kan fibration の持ち上げを取る。
規約：元のホーンから写像を構成する際の貼合せを追加仮定として結論に持ち込まない。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.12（Tag 00LV） の Hom 側の充填。 -/
lemma pathHollow_extension (hab : a < b) (i : Set.Ioo a b)
    {X : SSet.{u}} [SSet.KanComplex X] (f : (pathHollow hab i : SSet) ⟶ X) :
    ∃ g : nerve (Path a b) ⟶ X, (pathHollow hab i).ι ≫ g = f := by
  have : HasLiftingProperty (pathHollow hab i).ι (terminal.from X) :=
    pathHollow_anodyne hab i _ (by rwa [← fibration_iff])
  let sq : CommSq f (pathHollow hab i).ι (terminal.from X) (terminal.from _) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
