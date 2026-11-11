module
public import SerrePositivity.KST.Fibration.ZeroMiddleControlledFillerFamily
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSKanPrismIso

/-!
概要：同じ制御充填族の実三角柱を、元の二胞体へ戻る可逆な全パラメータ比較へ束ねる。
方針：同じ三角柱族の時間を並べ替え、全辺の厳密回収から元の可逆縦辺を得る。
規約：制御充填の存在は主張せず、その指定上側・元の終端・共有対角を保持する。
使われ方：K-6 c4 の再構成供給を指定 Verdier 上側の全族比較へ渡す利用側。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
  (K : SSet.{u + 1}) (F : (Δ[3] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (hF : ((horn 3 (2 : Fin 4)).ι ▷ K) ≫ F =
    fst (horn 3 (2 : Fin 4) : SSet.{u + 1}) K ≫ zeroMiddleFullSKanHorn s hZ)

/-- 概要：同じ三角柱族の時間とパラメータを、全族ホモトピーの順に並べる。
方針：同じ積の射影と組を使う。
規約：三角形・時間・元のパラメータを変更しない。
使われ方：元の制御三角柱族を実全族ホモトピーとして読む。 -/
def zeroMiddleControlledPrismShuffle : ((Δ[2] : SSet.{u + 1}) ⊗ K) ⊗ Δ[1] ⟶
    ((Δ[2] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ K :=
  lift (lift (fst (Δ[2] ⊗ K) Δ[1] ≫ fst Δ[2] K) (snd (Δ[2] ⊗ K) Δ[1]))
    (fst (Δ[2] ⊗ K) Δ[1] ≫ snd Δ[2] K)

/-- 概要：指定制御上側から元の native 二胞体へ戻る同じ実全族ホモトピー。
方針：元の制御三角柱族の始端・終端を同じ時間順で回収する。
規約：既存充填へ置き換えず、同じ F を使う。
使われ方：K-6 c4 の制御された上側全族の実比較。 -/
def zeroMiddleControlledPrismHomotopy : SSet.Homotopy
    ((stdSimplex.δ (2 : Fin 4) ▷ K) ≫ F)
    (fst (Δ[2] : SSet.{u + 1}) K ≫
      SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
        (Opposite.op ⦋2⦌) s)) where
  h := zeroMiddleControlledPrismShuffle K ≫ zeroMiddleControlledPrismFamily K F
  h₀ := by
    rw [← Category.assoc]
    change (SSet.ι₀ ▷ K) ≫ zeroMiddleControlledPrismFamily K F = _
    exact zeroMiddleControlledPrismFamily_zero K F
  h₁ := by
    rw [← Category.assoc]
    change (SSet.ι₁ ▷ K) ≫ zeroMiddleControlledPrismFamily K F = _
    exact zeroMiddleControlledPrismFamily_one s hZ K F hF
  rel := by ext n t; exact False.elim t.1.2

include hF in
/-- 概要：同じ全族ホモトピーの縦辺は元の三角柱の同じ実縦辺そのもの。
方針：三次元ホーンの全辺上の厳密回収を同じ縦辺の全一単体に適用する。
規約：ホモトピー類や端点だけの一致に弱めない。
使われ方：元の全 S• 比較の可逆性を同じ実制御三角柱へ移す。 -/
theorem zeroMiddleControlledPrismHomotopy_vertex_edge (v : (Δ[2] ⊗ K) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (zeroMiddleControlledPrismHomotopy s hZ K F hF) v).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (zeroMiddleFullSKanPrism s hZ) v.1).edge := by
  exact zeroMiddleControlledFillerFamily_one s hZ K F hF _

/-- 概要：同じ制御三角柱の全族比較は全パラメータ頂点で可逆。
方針：元の実縦辺の厳密回収と既証明の元の三角柱の可逆性を使う。
規約：同じ実ホモトピー自体を保持する。
使われ方：指定上側の全族を元の二胞体へ関手同型で戻す。 -/
theorem zeroMiddleControlledPrismHomotopy_pointwise :
    ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (zeroMiddleControlledPrismHomotopy s hZ K F hF) v).toTruncated := by
  intro v
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (zeroMiddleControlledPrismHomotopy_vertex_edge s hZ K F hF v)).mpr
      (zeroMiddleFullSKanPrism_pointwise s hZ v.1)

/-- 概要：同じ制御上側全族と元の指定 native 二胞体全族の実関手同型。
方針：同じ実三角柱の点ごとの可逆性を使う。
規約：制御充填の存在と指定全長 Hom の回収は未供給の別工程。
使われ方：K-6 c4 の再構成後の上側全族比較。 -/
def zeroMiddleControlledPrismFamilyIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((stdSimplex.δ (2 : Fin 4) ▷ K) ≫ F)
    (fst (Δ[2] : SSet.{u + 1}) K ≫
      SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app
        (Opposite.op ⦋2⦌) s)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy _
    (zeroMiddleControlledPrismHomotopy_pointwise s hZ K F hF)

/-- 概要：同じ実全族ホモトピーは制御上側の共有対角を全時刻固定する。
方針：元の中間三角柱の対角固定式を同じパラメータとともに評価する。
規約：同じ指定対角を全単体写像として保持する。
使われ方：指定上下二胞体の共有対角を合わせる際の実制限式。 -/
theorem zeroMiddleControlledPrismHomotopy_diagonal :
    ((stdSimplex.δ (1 : Fin 3) ▷ K) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (zeroMiddleControlledPrismHomotopy s hZ K F hF).h =
      fst ((Δ[1] : SSet.{u + 1}) ⊗ K) Δ[1] ≫
        (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ (stdSimplex.δ (2 : Fin 4) ▷ K) ≫ F := by
  ext n x
  have he := congrArg (fun G : ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⟶ Δ[3] =>
    G.app n (x.1.1, x.2)) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism_diagonal
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism.app n ((stdSimplex.δ (1 : Fin 3)).app n x.1.1, x.2) =
    (stdSimplex.δ (2 : Fin 4)).app n ((stdSimplex.δ (1 : Fin 3)).app n x.1.1) at he
  change F.app n (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism.app n ((stdSimplex.δ (1 : Fin 3)).app n x.1.1, x.2),
    x.1.2) = _
  rw [he]
  rfl

end SerrePositivity.KST.Fibration
