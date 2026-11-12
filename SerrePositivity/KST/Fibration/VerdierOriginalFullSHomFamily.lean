module
public import SerrePositivity.KST.Fibration.VerdierOriginalNativeHomFamily
public import SerrePositivity.KST.Fibration.ZeroFunctorFullSRelativeComparison
public import SerrePositivity.KST.Fibration.ZeroFunctorFullSCoreRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TrianglePathInterval

/-!
概要：指定 Verdier 両端で、同じ全 S• 比較とその core 制限を全 path のまま保持する。
方針：元の安定 Hom 族を同じ対象等号で戻してから全 S• 零値作用へ送る。
規約：同じ全 S• 比較を core へ制限する。独立な core 比較を選び直さない。
使われ方：K-6 c4 の動く上側短辺と共有対角の整合を保つ長 Hom 合成。
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

/-- 概要：元の上下安定 Hom 族を指定した同じ両端へ戻す。
方針：元の二対象の等号だけで全 Hom を輸送する。
規約：全 path を保持する。
使われ方：全 S• 作用と core 作用の共通の実入力。 -/
def verdierOriginalStableHomFamily (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u} ⟶ ((show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left) ⟶[SSet.{u}]
      (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)) :=
  verdierNullHomFamily d j ≫ eqToHom (congrArg₂ (fun (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) =>
    SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) A B)
      (verdierNullDiagonal_source d) (verdierNullDiagonal_target d))

private theorem zeroStableHom_vertex_transport {A B A' B' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (hA : A = A') (hB : B = B')
    (v : ((show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A) ⟶[SSet.{u}] (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from B)) _⦋0⦌)
    (hv : StableHomZeroVertex A B v) :
    StableHomZeroVertex A' B'
      ((eqToHom (congrArg₂ (fun (X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) =>
        SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) X Y) hA hB)).app (Opposite.op ⦋0⦌) v) := by
  cases hA
  cases hB
  exact hv

/-- 概要：指定両端へ戻した同じ全 path 族も全頂点で零値。
方針：元の各頂点の零値条件を同じ対象等号へ輸送する。
規約：零値関手の存在を新たに選ばない。
使われ方：同じ全 S• 零値作用への実代入。 -/
theorem verdierOriginalStableHomFamily_zero (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2)
    (v : (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}) _⦋0⦌) :
    StableHomZeroVertex d.left d.right
      ((verdierOriginalStableHomFamily d j).app (Opposite.op ⦋0⦌) v) :=
  zeroStableHom_vertex_transport (verdierNullDiagonal_source d) (verdierNullDiagonal_target d)
    _ (verdierNullHomFamily_zero d j v)

/-- 概要：指定両端の元の安定全 path 族は同じ直接端を持つ。
方針：元の共有対角上の一致を同じ Hom 輸送へ後合成する。
規約：元の直接端を保持する。
使われ方：全 S• 比較を直接端上で固定する境界。 -/
theorem verdierOriginalStableHomFamily_same_direct (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    coherentTriangleDirectVertexMap ≫ verdierOriginalStableHomFamily d j =
      coherentTriangleDirectVertexMap ≫ verdierOriginalStableHomFamily d k := by
  simp only [verdierOriginalStableHomFamily, ← Category.assoc]
  exact congrArg (fun f => f ≫ _) (verdierNullHomFamily_same_direct d j k)

/-- 概要：元の上下全 path を、指定両端の全 S• native Hom へ延長する。
方針：同じ安定 Hom の零値持ち上げと元の全 S• 作用を合成する。
規約：元の全 path を保持する。
使われ方：上側の動く全 S• 短辺を作る実入力。 -/
def verdierOriginalFullSHomFamily (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :=
  zeroStableHomFamilyLift (verdierOriginalStableHomFamily d j)
    (verdierOriginalStableHomFamily_zero d j) ≫ zeroFunctorFullSKanFamily d.left d.right

/-- 概要：同じ全 S• 延長の core 制限は元の指定両端の全 native Hom 族。
方針：元の全 S• 作用の core 回収と同じ零値持ち上げの回収を使う。
規約：全 path・全高次単体で元の族へ厳密に戻る。
使われ方：同じ全 S• 比較と core 比較を整合させる。 -/
theorem verdierOriginalFullSHomFamily_core (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    verdierOriginalFullSHomFamily d j ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)))).app
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj =
      verdierOriginalNativeHomFamily d j := by
  rw [verdierOriginalFullSHomFamily, Category.assoc, zeroFunctorFullSKanFamily_core,
    ← Category.assoc, zeroStableHomFamilyLift_recovery]
  exact Category.assoc _ _ _

/-- 概要：元の全 S• 上下 path 族の、直接端上で恒等の実比較。
方針：同じ安定全族を全 S• 相対比較へ代入する。
規約：core 比較はこの同じ比較の制限として使う。
使われ方：動く上側全 S• 短辺の合成端族。 -/
def verdierOriginalFullSHomComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    FixedRestrictionFunctorEdge coherentTriangleDirectVertexMap
      (verdierOriginalFullSHomFamily d j) (verdierOriginalFullSHomFamily d k) :=
  zeroFunctorFullSRelativeComparison _ _ _ (verdierOriginalStableHomFamily_zero d j)
    (verdierOriginalStableHomFamily_zero d k) (verdierOriginalStableHomFamily_same_direct d j k)

/-- 概要：同じ全 S• 比較を core に制限した元の上下全 path ホモトピー。
方針：同じ全円柱を元の core 包含で前合成し、両端だけを回収する。
規約：別の core 比較は選ばない。元の全円柱を保持する。
使われ方：実下側読出しとの境界付き合成に渡す始端比較。 -/
def verdierOriginalFullSCoreHomotopy (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    SSet.Homotopy (verdierOriginalNativeHomFamily d j) (verdierOriginalNativeHomFamily d k) where
  h := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (verdierOriginalFullSHomComparison d j k).edge).h ≫
    (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)))).app
      (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj
  h₀ := by
    rw [← Category.assoc, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge
      (verdierOriginalFullSHomComparison d j k).edge).h₀]
    exact verdierOriginalFullSHomFamily_core d j
  h₁ := by
    rw [← Category.assoc, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge
      (verdierOriginalFullSHomComparison d j k).edge).h₁]
    exact verdierOriginalFullSHomFamily_core d k
  rel := by ext n t; exact False.elim t.1.2

/-- 概要：同じ全 S• 比較の core 制限は直接端上で全時刻恒等。
方針：元の固定直接端条件を uncurry し、同じ core 制限へ後合成する。
規約：全時刻の写像の等号を保持し、成分の同型類へ弱めない。
使われ方：指定境界合成二単体の直接端の単位条件。 -/
theorem verdierOriginalFullSCoreHomotopy_direct (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    (coherentTriangleDirectVertexMap ▷ (Δ[1] : SSet.{u})) ≫
      (verdierOriginalFullSCoreHomotopy d j k).h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ coherentTriangleDirectVertexMap ≫
        verdierOriginalNativeHomFamily d j := by
  let E := verdierOriginalFullSHomComparison d j k
  have hs : (coherentTriangleDirectVertexMap ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge E.edge).h =
      fst (Δ[0] : SSet.{u}) Δ[1] ≫ coherentTriangleDirectVertexMap ≫
        verdierOriginalFullSHomFamily d j := by
    change (coherentTriangleDirectVertexMap ▷ (Δ[1] : SSet.{u})) ≫
      uncurry (SSet.yonedaEquiv.symm E.edge.edge) = _
    rw [← uncurry_pre_app, SSet.yonedaEquiv_symm_comp, E.restriction]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨x, t⟩
    dsimp [Truncated.Edge.id, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex, uncurry]
    rfl
  simpa only [Category.assoc, verdierOriginalFullSHomFamily_core] using!
    congrArg (fun f => f ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)))).app
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj) hs

/-- 概要：同じ全 S• 比較の全 path 合成端を読む実区間族。
方針：元の比較円柱を同じ合成 path の定値族へ制限する。
規約：元の比較そのものを保持する。
使われ方：K-6 c4 の上側第二短辺の動く実全族。 -/
def verdierOriginalFullSCompositePath (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :=
  lift (SSet.const (ComposableArrows.mk₀ coherentTriangleFullPath.{u}))
    (𝟙 (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (verdierOriginalFullSHomComparison d j k).edge).h

/-- 概要：同じ動く全 S• 合成端の core 制限は、同じ全 path 比較の合成端成分。
方針：同じ円柱の制限と core 後合成の結合則を使う。
規約：独立な合成端比較を選ばない。
使われ方：元の全 S• 短辺族と core 長 Hom 族の境界を整合させる。 -/
theorem verdierOriginalFullSCoreHomotopy_composite (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    lift (SSet.const (ComposableArrows.mk₀ coherentTriangleFullPath.{u}))
      (𝟙 (Δ[1] : SSet.{u})) ≫ (verdierOriginalFullSCoreHomotopy d j k).h =
      verdierOriginalFullSCompositePath d j k ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)))).app
          (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj :=
  (Category.assoc _ _ _).symm

end SerrePositivity.KST.Fibration
