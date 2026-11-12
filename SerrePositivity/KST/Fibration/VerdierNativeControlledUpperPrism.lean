module
public import SerrePositivity.KST.Fibration.ZeroMiddleNativeUpperBoundary
public import SerrePositivity.KST.Fibration.VerdierFullSUpperPrism

/-!
概要：実 (9b) の指定欠面を、同じ元の Verdier 上側へ対角を固定して戻す。
方針：同じ実三単体族の可逆三角柱を指定パラメータで制限する。
規約：固定三面内の既存比較を持つ同じ実充填を使い、充填を選び直さない。
使われ方：K-6 c4 の正規化四角柱の始端から元の指定上側への接続。
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
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (k : (Δ[1] : SSet.{u + 1}) _⦋0⦌)

/-- 概要：同じ実指定欠面から元の Verdier 上側へ戻る実三角柱。
方針：実供給三単体族の同じ可逆三角柱を元の指定時刻で読む。
規約：元の全二胞体を終端に厳密保持。使われ方：始端有限照合後の実比較。 -/
def verdierNativeControlledUpperPrism : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (zeroMiddleNativeUpperFamily (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d) Δ[1]) k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))) where
  h := ((lift (𝟙 (Δ[2] : SSet.{u + 1})) (SSet.const k)) ▷ Δ[1]) ≫
    (zeroMiddleControlledPrismHomotopy (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d) Δ[1]
      (zeroMiddleNativeFactorizationTetra (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d) Δ[1])
      (zeroMiddleNativeFactorizationTetra_horn (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d) Δ[1])).h
  h₀ := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc]
    rw [SSet.RelativeMorphism.Homotopy.h₀]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc]
    rw [SSet.RelativeMorphism.Homotopy.h₁]
    simp only [← Category.assoc, lift_fst, Category.id_comp]
    exact verdierFullSUpperPrism_original d
  rel := by ext n t; exact False.elim t.1.2

/-- 概要：同じ制御上側三角柱の各縦辺は元の可逆三角柱の同じ縦辺。
方針：指定パラメータでの前合成と退化辺の自然性を照合する。
規約：縦辺そのものの等号。使われ方：元の実可逆性の移送。 -/
theorem verdierNativeControlledUpperPrism_vertex (x : (Δ[2] : SSet.{u + 1}) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (verdierNativeControlledUpperPrism d k) x).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (zeroMiddleFullSKanPrism (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d)) x).edge := by
  have he := zeroMiddleControlledPrismHomotopy_vertex_edge (verdierUpperTriangle d)
    (verdierUpperTriangle_middle_isZero d) Δ[1]
    (zeroMiddleNativeFactorizationTetra (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d) Δ[1])
    (zeroMiddleNativeFactorizationTetra_horn (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d) Δ[1]) (x, k)
  change (zeroMiddleControlledPrismHomotopy (verdierUpperTriangle d)
    (verdierUpperTriangle_middle_isZero d) Δ[1]
    (zeroMiddleNativeFactorizationTetra (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d) Δ[1])
    (zeroMiddleNativeFactorizationTetra_horn (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d) Δ[1])).h.app (Opposite.op ⦋1⦌)
      (((lift (𝟙 (Δ[2] : SSet.{u + 1})) (SSet.const k)).app (Opposite.op ⦋1⦌)
        ((Δ[2] : SSet.{u + 1}).σ 0 x)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
  rw [σ_naturality_apply]
  have hk : (lift (𝟙 (Δ[2] : SSet.{u + 1})) (SSet.const k)).app (Opposite.op ⦋0⦌) x =
      (x, k) := by
    change (x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k 0) = (x, k)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
  rw [hk]
  exact he

/-- 概要：同じ実指定欠面から元の上側への三角柱は全頂点で可逆。
方針：元の同じ縦辺への厳密回収と既存の可逆性を使う。
規約：可逆性仮定なし。使われ方：始端四角形を元の Verdier 四角形へ戻す。 -/
theorem verdierNativeControlledUpperPrism_pointwise :
    ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (verdierNativeControlledUpperPrism d k) x).toTruncated := by
  intro x
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (verdierNativeControlledUpperPrism_vertex d k x)).mpr
    (zeroMiddleFullSKanPrism_pointwise (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d) x)

/-- 概要：同じ実制御三角柱は指定共有対角を全時刻で固定する。
方針：元の中間三角柱の対角回収を同じパラメータへ評価する。
規約：端点だけでなく全対角族の厳密等式。
使われ方：元の下側を固定した四角柱の貼り合わせ。 -/
theorem verdierNativeControlledUpperPrism_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (verdierNativeControlledUpperPrism d k).h =
      fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ stdSimplex.δ (1 : Fin 3) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (zeroMiddleNativeUpperFamily (verdierUpperTriangle d)
          (verdierUpperTriangle_middle_isZero d) Δ[1]) k := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  have he := congrArg (fun G : ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⟶ Δ[3] => G.app n x)
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism_diagonal
  change (zeroMiddleNativeFactorizationTetra (verdierUpperTriangle d)
    (verdierUpperTriangle_middle_isZero d) Δ[1]).app n
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism.app n ((stdSimplex.δ (1 : Fin 3)).app n x.1, x.2),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k n.unop.len) = _
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism.app n ((stdSimplex.δ (1 : Fin 3)).app n x.1, x.2) =
    (stdSimplex.δ (2 : Fin 4)).app n ((stdSimplex.δ (1 : Fin 3)).app n x.1) at he
  exact congrArg (fun z => (zeroMiddleNativeFactorizationTetra (verdierUpperTriangle d)
    (verdierUpperTriangle_middle_isZero d) Δ[1]).app n
      (z, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k n.unop.len)) he

/-- 概要：同じ指定欠面から元の指定上側への実全関手同型。
方針：同じ対角固定三角柱の全縦辺可逆性を適用する。
規約：実 (9b) の同じ充填を保持する。使われ方：有限始端照合後の実比較。 -/
def verdierNativeControlledUpperPrismIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (zeroMiddleNativeUpperFamily (verdierUpperTriangle d)
      (verdierUpperTriangle_middle_isZero d) Δ[1]) k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy _ (verdierNativeControlledUpperPrism_pointwise d k)

end SerrePositivity.KST.Fibration
