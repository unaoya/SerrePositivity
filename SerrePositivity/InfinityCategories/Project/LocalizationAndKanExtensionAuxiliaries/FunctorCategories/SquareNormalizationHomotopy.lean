module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.CompositionSquareCollapse
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.RightHomotopySquare

/-!
概要：畳んだ正方形から元の正方形へ戻る具体的な変形。
方針：(s,t,v) を (min(s,max(t,v)),t) に送り、四辺を計算する。
規約：時間は第三因子。上辺・左辺を固定し、右辺は元の下側三角形を通る。
使われ方：B1 の比較で正方形全体と境界の経路を同時に保持する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：正方形の右下の頂点を時間とともに戻す第一座標。
方針：有限全順序の min と max を使う。
規約：入力は ((横,縦),時間)。
使われ方：正方形の正規化の具体的なホモトピー。 -/
def squareNormalizationFirstOrder : (Fin 2 × Fin 2) × Fin 2 →o Fin 2 where
  toFun p := min p.1.1 (max p.1.2 p.2)
  monotone' := by decide

/-- 概要：正方形の正規化を恒等射へ戻す円柱の射。
方針：第一座標に単調写像、第二座標に元の縦座標を使う。
規約：第三因子が時間。
使われ方：正方形を値域とする図式の具体的変形。 -/
def squareNormalizationCylinder :
    (((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1]) ⟶ (Δ[1] : SSet.{u}) ⊗ Δ[1] :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexTripleProductMap squareNormalizationFirstOrder)
    (fst _ (Δ[1] : SSet.{u}) ≫ snd (Δ[1] : SSet.{u}) Δ[1])

/-- 概要：時間零では上側の三角形への畳み込み。
方針：二つの座標を頂点ごとに有限計算する。
規約：下辺を最初の頂点へ畳む。
使われ方：元の正方形の正規化を始点とする。 -/
lemma squareNormalizationCylinder_zero :
    SSet.ι₀ ≫ squareNormalizationCylinder.{u} = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareUpperFold ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext <;> apply SSet.yonedaEquiv.injective <;>
    apply Prod.ext <;> decide

/-- 概要：時間一では元の正方形の恒等射。
方針：min(s,max(t,1))=s を頂点で使う。
規約：終点の図式を厳密に回収する。
使われ方：正規化から元の正方形へ戻す変形の終点。 -/
lemma squareNormalizationCylinder_one :
    SSet.ι₁ ≫ squareNormalizationCylinder.{u} = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext <;> apply SSet.yonedaEquiv.injective <;>
    apply Prod.ext <;> decide

/-- 概要：上辺は正規化の全時間で固定される。
方針：正方形の二単体で有限計算する。
規約：第一因子が辺、第二因子が時間。
使われ方：正方形の上辺の代表を保持する。 -/
lemma squareNormalizationCylinder_top :
    ((SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫
      squareNormalizationCylinder = fst _ (Δ[1] : SSet.{u}) ≫ SSet.ι₁ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext <;> apply SSet.yonedaEquiv.injective <;>
    apply Prod.ext <;> decide

/-- 概要：左辺は正規化の全時間で固定される。
方針：正方形の二単体で有限計算する。
規約：左辺を構成する写像を厳密に保持する。
使われ方：単位成分の代表を変えない比較。 -/
lemma squareNormalizationCylinder_left :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      squareNormalizationCylinder = fst _ (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext <;> apply SSet.yonedaEquiv.injective <;>
    apply Prod.ext <;> decide

/-- 概要：下辺の変形に現れる横座標の単調写像。
方針：横座標と時間の小さい方を取る。
規約：下辺内での収縮。
使われ方：恒等辺を値に持つ下辺が全時間で固定されることの確認。 -/
def squareNormalizationBottomOrder : Fin 2 × Fin 2 →o Fin 2 where
  toFun p := min p.1 p.2
  monotone' := by decide

/-- 概要：下辺の変形は下辺の中を通る。
方針：正方形の二単体で有限計算する。
規約：底の図式が定値なら変形も定値となる。
使われ方：comma 正方形の退化した下辺を固定する。 -/
lemma squareNormalizationCylinder_bottom :
    ((SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫
      squareNormalizationCylinder = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexProductMap squareNormalizationBottomOrder ≫ SSet.ι₀ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext <;> apply SSet.yonedaEquiv.injective <;>
    apply Prod.ext <;> decide

/-- 概要：右辺の変形は元の下側三角形の右ホモトピーを通る。
方針：正方形の二単体で二つの具体的な射を照合する。
規約：下側の二単体の情報を指定したまま保持する。
使われ方：正方形全体の変形から右辺の経路を厳密に取り出す。 -/
lemma squareNormalizationCylinder_right :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
      squareNormalizationCylinder = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.rightHomotopySquare ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext <;> apply SSet.yonedaEquiv.injective <;>
    apply Prod.ext <;> decide

/-- 概要：上側三角形から補完した正方形は元の正方形にホモトピック。
方針：具体的な正方形の正規化円柱を元の図式で後合成する。
規約：quasicategory 性を使わず、元の下側の二単体を変形に保持する。
使われ方：B1 の comma の族の復元と元の正方形を比較する。 -/
noncomputable def FunctorCompositionSquare.normalizationHomotopy {A X : SSet.{u}}
    {U V W : A ⟶ X} {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d : SSet.Homotopy U W} (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle Q.upperTriangle).diagram Q.diagram where
  h := squareNormalizationCylinder ≫ Q.diagram
  h₀ := by
    rw [← Category.assoc, squareNormalizationCylinder_zero, Category.assoc]
    exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle_eq_fold Q.upperTriangle).symm
  h₁ := by
    rw [← Category.assoc, squareNormalizationCylinder_one, Category.id_comp]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：正方形全体の変形は上辺の代表を固定する。
方針：正規化円柱の上辺の公式を後合成する。
規約：時間方向の射の等式。
使われ方：G の標的辺を保つ比較。 -/
lemma FunctorCompositionSquare.normalizationHomotopy_top {A X : SSet.{u}}
    {U V W : A ⟶ X} {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d : SSet.Homotopy U W} (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d) :
    ((SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫
      Q.normalizationHomotopy.h = fst _ (Δ[1] : SSet.{u}) ≫ curry r.h := by
  change _ ≫ (squareNormalizationCylinder ≫ Q.diagram) = _
  rw [← Category.assoc, squareNormalizationCylinder_top, Category.assoc, Q.top]

/-- 概要：正方形全体の変形は左辺の代表を固定する。
方針：正規化円柱の左辺の公式を後合成する。
規約：時間方向の射の等式。
使われ方：単位成分を保つ比較。 -/
lemma FunctorCompositionSquare.normalizationHomotopy_left {A X : SSet.{u}}
    {U V W : A ⟶ X} {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d : SSet.Homotopy U W} (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫ Q.normalizationHomotopy.h =
      fst _ (Δ[1] : SSet.{u}) ≫ curry l.h := by
  change _ ≫ (squareNormalizationCylinder ≫ Q.diagram) = _
  rw [← Category.assoc, squareNormalizationCylinder_left, Category.assoc, Q.left]

/-- 概要：下辺が恒等の正方形の正規化は下辺を全時間で固定する。
方針：変形が下辺内を通ることと、下辺の定値性を使う。
規約：恒等辺の代表そのものに定値。
使われ方：comma 正方形の境界を固定する比較。 -/
lemma FunctorCompositionSquare.normalizationHomotopy_bottom {A X : SSet.{u}}
    {U V W : A ⟶ X} {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d : SSet.Homotopy U W} (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d) :
    ((SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫
      Q.normalizationHomotopy.h = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) := by
  change _ ≫ (squareNormalizationCylinder ≫ Q.diagram) = _
  rw [← Category.assoc, squareNormalizationCylinder_bottom, Category.assoc, Q.bottom,
    SSet.comp_const]

/-- 概要：正方形全体の変形の右辺は元の下側の二単体を通る経路。
方針：円柱の右辺の具体公式を後合成する。
規約：元の二単体そのものへの因子分解を保持する。
使われ方：導来 fiber の path 座標と正方形全体の変形を照合する。 -/
lemma FunctorCompositionSquare.normalizationHomotopy_right {A X : SSet.{u}}
    {U V W : A ⟶ X} {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d : SSet.Homotopy U W} (Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫ Q.normalizationHomotopy.h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.rightHomotopySquare ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ Q.diagram := by
  change _ ≫ (squareNormalizationCylinder ≫ Q.diagram) = _
  rw [← Category.assoc, squareNormalizationCylinder_right, Category.assoc]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
