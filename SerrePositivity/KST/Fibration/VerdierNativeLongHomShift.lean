module
public import SerrePositivity.KST.Fibration.VerdierOriginalCompositeNativeEdge
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.ConstantEdgeFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TrianglePathInterval
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-!
概要：指定 Verdier 両端の長 Hom 全族を、元の実合成端比較で上側の指定合成端へ移す。
方針：同じ native path 区間族と元の実比較辺の定数族を、全関手 Kan 複体で合成する。
規約：元の比較辺と全パラメータを保持する。新しい存在入力は追加しない。
使われ方：K-6 c4 の下側長 Hom 読出しから上側再構成へ渡す実入力の準備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 概要：元の指定 Verdier 両端の core Kan native Hom。
方針：同じ元の二対象を core single Kan 座標と宇宙持ち上げへ送る。
規約：元の対象を保持する。
使われ方：合成端を合わせる長 Hom 全族の標的。 -/
abbrev verdierNativeLongHomTarget (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :=
  (SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
      (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)))

/-- 概要：元の指定合成完全射の同じ native core Kan 頂点。
方針：同じ実完全射の core S• 作用の豊穣頂点を持ち上げる。
規約：上下の元の合成端を選び直さない。
使われ方：長 Hom 全族が保持する実合成端。 -/
def verdierNativeCompositePoint (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    (verdierNativeLongHomTarget d) _⦋0⦌ :=
  ULift.up (SimplicialCategory.homEquiv' _ _
    (stableCoreSingleKanMap (verdierNullCompositeOriginalMap d j)))

variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (K : SSet.{u + 1})
  (q : K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj
    (verdierNativeLongHomTarget d))

/-- 概要：元の長 Hom 全族の、同じ native 区間座標での直接端。
方針：同じ path 区間同型の始点で全族を評価する。
規約：K の各頂点だけに制限しない。
使われ方：合成端の移送で厳密保持する共有対角の入力族。 -/
def verdierNativeLongHomStart :=
  (q ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso.{u, u + 1}.inv).app
    (verdierNativeLongHomTarget d)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))

variable (hq : q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
  (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
    SSet.const (verdierNativeCompositePoint d 1))

/-- 概要：同じ長 Hom 全族は、直接端から元の下側合成端への実ホモトピー。
方針：元の path 区間座標を転置し、終点回収へ元の全族合成端等式を代入する。
規約：全時刻・全入力を保持し、読み出した直接端を選び直さない。
使われ方：元の実合成端比較との全関手 Kan 複体内の合成。 -/
def verdierNativeLongHomInitialHomotopy : SSet.Homotopy
    (verdierNativeLongHomStart d K q) (SSet.const (verdierNativeCompositePoint d 1)) := by
  let Q := q ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso.{u, u + 1}.inv).app
    (verdierNativeLongHomTarget d)
  refine { h := (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ uncurry Q
           h₀ := ?_, h₁ := ?_, rel := ?_ }
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  · have he : Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        SSet.const (verdierNativeCompositePoint d 1) := by
      dsimp only [Q]
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso_inv_last]
      exact hq
    calc
      _ = Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro k
        rfl
      _ = _ := he
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：元の下側合成端から上側合成端への同じ実辺の定数パラメータ族。
方針：元の指定比較辺を既存の全区間族へ送る。
規約：元の比較円柱の実辺そのものを保持する。
使われ方：長 Hom 全族へ続ける実合成端比較。 -/
def verdierNativeCompositeConstantEdge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge
    (SSet.Edge.ofTruncated (X := verdierNativeLongHomTarget d)
      (verdierNativeOriginalCompositeEdge d 1 0))))

/-- 概要：元の長 Hom 全族に同じ実合成端比較を続けた全関手辺。
方針：既存の Kan 関手複体で同じ二辺を合成する。
規約：全パラメータの直接端を保持する。
使われ方：上側合成端を持つ同じ長 Hom 全族の構成。 -/
def verdierNativeLongHomShiftEdge :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (verdierNativeLongHomInitialHomotopy d K q hq)).comp
    (verdierNativeCompositeConstantEdge d K)

/-- 概要：同じ二辺の合成を認証する元の全関手二単体。
方針：同じ選択済み合成の CompStruct を保持する。
規約：長 Hom 全族と元の実合成端辺を記録し、合成辺だけに弱めない。
使われ方：共有対角の比較を元の合成端比較とともに戻す。 -/
def verdierNativeLongHomShiftTriangle :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (verdierNativeLongHomInitialHomotopy d K q hq)).compStruct
    (verdierNativeCompositeConstantEdge d K)

/-- 概要：同じ合成辺から元のパラメータを持つ区間族を取り出す。
方針：全関手辺の実ホモトピーを転置する。
規約：各入力点で辺を選び直さない。
使われ方：同じ native path 座標へ戻す前の全長 Hom 族。 -/
def verdierNativeLongHomShiftInterval :
    K ⟶ (ihom (Δ[1] : SSet.{u + 1})).obj (verdierNativeLongHomTarget d) :=
  curry ((β_ (Δ[1] : SSet.{u + 1}) K).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (verdierNativeLongHomShiftEdge d K q hq)).h)

/-- 概要：同じ区間族の実ホモトピーは元の合成辺のホモトピーそのもの。
方針：curry・uncurry の回収と同じ対称性の往復を使う。
規約：元の全関手辺を厳密に回収する。
使われ方：直接端と合成端の同じ全族での回収。 -/
theorem verdierNativeLongHomShiftInterval_homotopy :
    (β_ K (Δ[1] : SSet.{u + 1})).hom ≫
      uncurry (verdierNativeLongHomShiftInterval d K q hq) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (verdierNativeLongHomShiftEdge d K q hq)).h := by
  rw [verdierNativeLongHomShiftInterval, uncurry_curry, ← Category.assoc]
  simp

/-- 概要：同じ区間族は元の直接端を保持し、上側の元の実合成端へ終わる。
方針：同じ全ホモトピーの両端を固定頂点評価として読む。
規約：各頂点だけでなく全パラメータの射の等式。
使われ方：移送後の長 Hom 全族の入力境界を確認する。 -/
theorem verdierNativeLongHomShiftInterval_endpoints :
    (verdierNativeLongHomShiftInterval d K q hq ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        verdierNativeLongHomStart d K q) ∧
    (verdierNativeLongHomShiftInterval d K q hq ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        SSet.const (verdierNativeCompositePoint d 0)) := by
  constructor
  · calc
      _ = SSet.ι₀ ≫ ((β_ K (Δ[1] : SSet.{u + 1})).hom ≫
          uncurry (verdierNativeLongHomShiftInterval d K q hq)) := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro k
        rfl
      _ = _ := (congrArg (fun h => SSet.ι₀ ≫ h)
        (verdierNativeLongHomShiftInterval_homotopy d K q hq)).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (verdierNativeLongHomShiftEdge d K q hq)).h₀
  · calc
      _ = SSet.ι₁ ≫ ((β_ K (Δ[1] : SSet.{u + 1})).hom ≫
          uncurry (verdierNativeLongHomShiftInterval d K q hq)) := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro k
        rfl
      _ = _ := (congrArg (fun h => SSet.ι₁ ≫ h)
        (verdierNativeLongHomShiftInterval_homotopy d K q hq)).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (verdierNativeLongHomShiftEdge d K q hq)).h₁

/-- 概要：移送後の同じ区間族を元の native path 座標へ戻す。
方針：元と同じ path 区間同型で前合成する。
規約：全長 Hom の始域・宇宙を元の入力と合わせる。
使われ方：上側の指定合成端を持つ実長 Hom 入力。 -/
def verdierNativeLongHomShiftFamily :=
  verdierNativeLongHomShiftInterval d K q hq ≫
    (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso.{u, u + 1}.hom).app (verdierNativeLongHomTarget d)

/-- 概要：移送後の native path 族を同じ区間座標へ読むと元の移送区間族へ厳密に戻る。
方針：同じ内部 Hom の同型の順逆の回収を使う。
規約：入力点や代表辺を選び直さない。
使われ方：元の native 合成端と直接端の評価への代入。 -/
theorem verdierNativeLongHomShiftFamily_rebase :
    verdierNativeLongHomShiftFamily d K q hq ≫
      (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso.{u, u + 1}.inv).app
        (verdierNativeLongHomTarget d) = verdierNativeLongHomShiftInterval d K q hq := by
  have hc : (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso.{u, u + 1}.hom).app
      (verdierNativeLongHomTarget d) ≫
        (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso.{u, u + 1}.inv).app
          (verdierNativeLongHomTarget d) = 𝟙 _ :=
    ((internalHom.mapIso _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso.{u, u + 1}.op).app
      (verdierNativeLongHomTarget d)).hom_inv_id
  rw [verdierNativeLongHomShiftFamily, Category.assoc, hc, Category.comp_id]

/-- 概要：移送後の native 長 Hom 全族は元の直接端を全入力で厳密保持する。
方針：同じ区間座標への回収と同じ合成ホモトピーの始端回収を使う。
規約：パラメータの頂点だけの等号に弱めない。
使われ方：正規化した上下族の共有対角を保持する実入力。 -/
theorem verdierNativeLongHomShiftFamily_start :
    verdierNativeLongHomStart d K (verdierNativeLongHomShiftFamily d K q hq) =
      verdierNativeLongHomStart d K q := by
  unfold verdierNativeLongHomStart
  rw [verdierNativeLongHomShiftFamily_rebase]
  exact (verdierNativeLongHomShiftInterval_endpoints d K q hq).1

/-- 概要：移送後の native 長 Hom 全族は元の上側合成端へ全入力で厳密に戻る。
方針：元の path の全体頂点を区間終点として評価する。
規約：元の実合成完全射の core S• Kan 作用を保持する。
使われ方：上側再構成空間へ入れる指定合成端条件。 -/
theorem verdierNativeLongHomShiftFamily_full :
    verdierNativeLongHomShiftFamily d K q hq ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
        SSet.const (verdierNativeCompositePoint d 0) := by
  have he : (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso.{u, u + 1}.inv).app
      (verdierNativeLongHomTarget d) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso_inv_last]
  calc
    _ = verdierNativeLongHomShiftFamily d K q hq ≫
        ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso.{u, u + 1}.inv).app
          (verdierNativeLongHomTarget d) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :=
      congrArg (fun e => verdierNativeLongHomShiftFamily d K q hq ≫ e) he.symm
    _ = (verdierNativeLongHomShiftFamily d K q hq ≫
        (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso.{u, u + 1}.inv).app
          (verdierNativeLongHomTarget d)) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
      (Category.assoc _ _ _).symm
    _ = _ := (congrArg (fun e => e ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
        (verdierNativeLongHomShiftFamily_rebase d K q hq)).trans
        (verdierNativeLongHomShiftInterval_endpoints d K q hq).2

/-- 概要：移送後の同じ native 長 Hom 族は、再構成仕様の直接 path で元の全族を厳密回収する。
方針：元と同じ区間始点を二端点だけの path へ計算し、全族の始端保存へ代入する。
規約：K の非退化単体を含む射の等号を保持する。
使われ方：正規化後の上下二胞体の共有対角を全族で貼る。 -/
theorem verdierNativeLongHomShiftFamily_direct :
    let direct : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} :=
      { I := {ULift.up 0, ULift.up 2}
        left := by simp
        right := by simp
        left_le := fun k _ => Fin.zero_le k.down
        le_right := fun k _ => Fin.le_last k.down }
    verdierNativeLongHomShiftFamily d K q hq ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (ULift.up (ComposableArrows.mk₀ direct)) =
        q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ direct)) := by
  let direct : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} :=
    { I := {ULift.up 0, ULift.up 2}
      left := by simp
      right := by simp
      left_le := fun k _ => Fin.zero_le k.down
      le_right := fun k _ => Fin.le_last k.down }
  change verdierNativeLongHomShiftFamily d K q hq ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (ULift.up (ComposableArrows.mk₀ direct)) =
      q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ direct))
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso.{u, u + 1}.inv.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        ULift.up (ComposableArrows.mk₀ direct) := by
    change ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso.inv.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = _
    apply ULift.ext
    apply CategoryTheory.Functor.ext (fun i => ?_)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathFromInterval (ULift.up (0 : Fin 2)) = direct
    apply SimplicialThickening.Path.ext
    ext ⟨k⟩
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathFromInterval, direct]
  have he : (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.uliftTriangleNativePathIntervalIso.{u, u + 1}.inv).app
      (verdierNativeLongHomTarget d) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ direct)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre, hp]
  have hs (q₀ : K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierNativeLongHomTarget d)) :
      verdierNativeLongHomStart d K q₀ =
        q₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ direct)) :=
    (Category.assoc _ _ _).trans (congrArg (fun e => q₀ ≫ e) he)
  exact (hs (verdierNativeLongHomShiftFamily d K q hq)).symm.trans
    ((verdierNativeLongHomShiftFamily_start d K q hq).trans (hs q))

end SerrePositivity.KST.Fibration
