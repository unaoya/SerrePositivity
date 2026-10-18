module

public import SerrePositivity.InfinityCategories.Core.InitialCofinality
public import SerrePositivity.InfinityCategories.Core.TerminalTransport
public import SerrePositivity.InfinityCategories.Derived.ConeEdgeCompatibility

/-! # 始対象の値による指定極限錐の計算

概要：二宇宙の cofinality を使い、始対象からの標準錐を極限錐にする。
方針：一点図式の恒等錐の終対象性を外側ホーンで検証し、制限で反映する。
規約：極限の比較は h(sliceOver) に保持する。
使われ方：Π2-5 の指定 perfectoid 化との比較。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- 一点図式の恒等錐は slice の終対象である。 -/
theorem sliceIdentityCone_terminal {X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌) :
    IsTerminalVertex (sliceIdentityCone x) := by
  intro n b hb
  let L := sliceOverUncurry b
  let σ := (finalHornPointJoinIso (n + 1)).inv ≫ L
  let e := SSet.Truncated.Edge.id (X := (truncation 2).obj X) x
  have he : IsInvertibleEdge e := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk e)
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  have hσ : σ.app (Opposite.op ⦋1⦌) (finalHornEdge n) = e.edge := by
    rw [← finalHornPointJoinIso_edge, ← SSet.yonedaEquiv_comp]
    change SSet.yonedaEquiv (((joinStdSimplexIso 0 0).inv ≫
      joinMap (boundaryVertex n (Fin.last (n + 1))) (𝟙 Δ[0]) ≫
        (finalHornPointJoinIso (n + 1)).hom) ≫
          ((finalHornPointJoinIso (n + 1)).inv ≫ L)) = _
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
    change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      (joinMap (boundaryVertex n (Fin.last (n + 1))) (𝟙 Δ[0]) ≫ sliceOverUncurry b)) = _
    rw [← sliceOverUncurry_precomp, hb, sliceOverUncurry_yoneda]
    rw [sliceIdentityCone, SSet.comp_const]
    change X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op x =
      X.map (SimplexCategory.σ (0 : Fin 1)).op x
    exact congrArg (fun α : ⦋1⦌ ⟶ ⦋0⦌ => X.map α.op x) (by decide)
  obtain ⟨G, hG⟩ := hasFinalHornFillers_of_isInvertibleEdge e he n σ hσ
  let M := (joinStdSimplexIso (n + 1) 0).hom ≫ G
  have hM : joinMap (boundary (n + 1)).ι (𝟙 Δ[0]) ≫ M = L := by
    change joinMap (boundary (n + 1)).ι (𝟙 Δ[0]) ≫
      (joinStdSimplexIso (n + 1) 0).hom ≫ G = L
    rw [← Category.assoc, ← finalHornPointJoinIso_hom_ι, Category.assoc, hG]
    exact (finalHornPointJoinIso (n + 1)).hom_inv_id_assoc L
  have hfixed : joinInr Δ[n + 1] Δ[0] ≫ M = SSet.yonedaEquiv.symm x := by
    rw [← sliceOverUncurry_fixed b]
    change joinInr Δ[n + 1] Δ[0] ≫ M = joinInr (boundary (n + 1) : SSet) Δ[0] ≫ L
    rw [← hM]
    simp only [← Category.assoc, joinInr_joinMap, Category.id_comp]
  refine ⟨sliceOverCurry M hfixed, ?_⟩
  rw [sliceOverCurry_precomp]
  have heq : sliceOverCurry (joinMap (boundary (n + 1)).ι (𝟙 Δ[0]) ≫ M)
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp, hfixed]) =
      sliceOverCurry (sliceOverUncurry b) (sliceOverUncurry_fixed b) := by
    congr 1
  exact heq.trans (sliceOverCurry_uncurry b)

/-- 始対象を全射列に前置して得る標準錐。 -/
def initialValueCone {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} (F : nerve I ⟶ X) : JoinCone F :=
  ⟨nerveInitialCone hc ≫ F, by rw [← Category.assoc, nerveInitialCone_inr, Category.id_comp]⟩

/-- 始対象で制限した標準錐の射は定数射。 -/
theorem initialValueCone_restriction {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} (F : nerve I ⟶ X) :
    ((initialRestriction F c).app (Opposite.op ⦋0⦌) (initialValueCone hc F)).val =
      SSet.const (F.app _ (nerveVertex c)) := by
  change joinMap (𝟙 Δ[0]) (nervePoint c) ≫ (nerveInitialCone hc ≫ F) = _
  rw [← Category.assoc, nerveInitialCone_at_point, SSet.const_comp]

/-- 二宇宙版の cofinality により始対象の値の標準錐が極限になる。 -/
theorem initialValueCone_isLimit {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X) :
    IsLimitCone (initialValueCone hc F) := by
  have := initialCofinality hc F
  apply isTerminalVertex_of_trivialKanFibration (initialRestriction F c)
  have hp : nervePoint c ≫ F = SSet.yonedaEquiv.symm (F.app _ (nerveVertex c)) := by
    rw [nervePoint, SSet.yonedaEquiv_symm_comp]
  let d := JoinCone.cast (sliceIdentityCone (F.app _ (nerveVertex c))) hp.symm
  have hd : IsLimitCone d := IsLimitCone.cast (c := sliceIdentityCone (F.app _ (nerveVertex c)))
    (sliceIdentityCone_terminal (F.app _ (nerveVertex c))) hp.symm
  have ht : (initialRestriction F c).app (Opposite.op ⦋0⦌) (initialValueCone hc F) = d :=
    Subtype.ext (initialValueCone_restriction hc F)
  rw [ht]
  exact hd

/-- 辺のホモトピー圏上で単体的射を作用させる。 -/
def coneHomotopyMap {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (q : X ⟶ Y) :=
  (homotopyCategoryBridge X).functor ⋙ (hoFunctor.map q).toFunctor ⋙
    (homotopyCategoryBridge Y).inverse

/-- この作用は辺の像そのものを与える。 -/
theorem coneHomotopyMap_homMk {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (q : X ⟶ Y) {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    (coneHomotopyMap q).map (SSet.Truncated.HomotopyCategory₂.homMk e) =
      SSet.Truncated.HomotopyCategory₂.homMk (e.map ((truncation 2).map q)) := by
  change (pathToEdgeHomotopyCategory _).map
    ((SSet.Truncated.mapHomotopyCategory ((truncation 2).map q)).map
      (SSet.Truncated.HomotopyCategory.homMk e)) = _
  rw [SSet.Truncated.mapHomotopyCategory_homMk]
  simp only [pathToEdgeHomotopyCategory, SSet.Truncated.HomotopyCategory.lift_map_homMk]

/-- 一単体が一致する辺の可逆性は、端点の表示によらない。 -/
theorem coneEdge_isIso_of_edge_eq {X : SSet.{u}} [Quasicategory X]
    {x y x' y' : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (e' : SSet.Truncated.Edge (X := (truncation 2).obj X) x' y')
    (h : e.edge = e'.edge) [IsIso (SSet.Truncated.HomotopyCategory₂.homMk e')] :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk e) := by
  have hs : x = x' := e.src_eq.symm.trans ((congrArg _ h).trans e'.src_eq)
  have ht : y = y' := e.tgt_eq.symm.trans ((congrArg _ h).trans e'.tgt_eq)
  subst x' y'
  have hh : e = e' := SSet.Truncated.Edge.ext h
  rw [hh]
  infer_instance

/-- 標準錐の始対象への脚は退化した恒等一単体である。 -/
theorem initialValueCone_leg {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} (F : nerve I ⟶ X) :
    (derivedConeLeg (initialValueCone hc F) (nerveVertex c)).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) (F.app _ (nerveVertex c))).edge := by
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    joinMap (𝟙 Δ[0]) (nervePoint c) ≫ (nerveInitialCone hc ≫ F)) = _
  rw [← Category.assoc (joinMap _ _) _ _, nerveInitialCone_at_point, SSet.const_comp,
    SSet.comp_const]
  change X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op _ =
    X.map (SimplexCategory.σ (0 : Fin 1)).op _
  exact congrArg (fun α : ⦋1⦌ ⟶ ⦋0⦌ => X.map α.op (F.app _ (nerveVertex c))) (by decide)

/-- 指定錐と始対象の値の標準錐との同型は h(sliceOver F) にある。 -/
def initialLimitConeIso {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : JoinCone F) (ha : IsLimitCone a) :
    (SSet.HomotopyCategory.mk a : hoFunctor.obj (sliceOver F)) ≅
      SSet.HomotopyCategory.mk (initialValueCone hc F) :=
  limitConeIso a (initialValueCone hc F) ha (initialValueCone_isLimit hc F)

/-- 極限錐の比較同型を表す slice の辺を選ぶ。 -/
def initialLimitConeEdge {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : JoinCone F) (ha : IsLimitCone a) :
    SSet.Truncated.Edge (X := (truncation 2).obj (sliceOver F)) a (initialValueCone hc F) :=
  Classical.choose (SSet.Truncated.HomotopyCategory₂.homMk_surjective
    (terminalVertexIso₂ ha (initialValueCone_isLimit hc F)).hom)

/-- 選んだ辺の類は、二次切断で計算した同じ比較同型である。 -/
theorem initialLimitConeEdge_homMk {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : JoinCone F) (ha : IsLimitCone a) :
    SSet.Truncated.HomotopyCategory₂.homMk (initialLimitConeEdge hc F a ha) =
      (terminalVertexIso₂ ha (initialValueCone_isLimit hc F)).hom :=
  Classical.choose_spec (SSet.Truncated.HomotopyCategory₂.homMk_surjective
    (terminalVertexIso₂ ha (initialValueCone_isLimit hc F)).hom)

/-- slice の比較辺は、公開した h(sliceOver) の比較同型そのものを表す。 -/
theorem initialLimitConeEdge_path {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : JoinCone F) (ha : IsLimitCone a) :
    (homotopyCategoryBridge (sliceOver F)).functor.map
        (SSet.Truncated.HomotopyCategory₂.homMk (initialLimitConeEdge hc F a ha)) =
      (initialLimitConeIso hc F a ha).hom := by
  rw [initialLimitConeEdge_homMk]
  rfl

/-- 比較同型の頂点への射影は、指定した各脚と三角形で両立する。 -/
theorem initialLimitConeEdge_leg {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : JoinCone F) (ha : IsLimitCone a) (t : (nerve I) _⦋0⦌) :
    SSet.Truncated.HomotopyCategory₂.homMk
        ((initialLimitConeEdge hc F a ha).map ((truncation 2).map (sliceOverProjection F))) ≫
      SSet.Truncated.HomotopyCategory₂.homMk (derivedConeLeg (initialValueCone hc F) t) =
        SSet.Truncated.HomotopyCategory₂.homMk (derivedConeLeg a t) :=
  derivedConeLeg_homMk_comp (initialLimitConeEdge hc F a ha) t

/-- 極限錐の始対象への実際の脚は導来同値を表す。 -/
theorem initialLimitLeg_isIso {I : Type v} [Category.{w} I] {c : I} (hc : IsInitial c)
    {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X)
    (a : JoinCone F) (ha : IsLimitCone a) :
    IsIso (SSet.Truncated.HomotopyCategory₂.homMk (derivedConeLeg a (nerveVertex c))) := by
  let e := initialLimitConeEdge hc F a ha
  have hi : IsIso (SSet.Truncated.HomotopyCategory₂.homMk e) := by
    rw [initialLimitConeEdge_homMk]
    infer_instance
  have hi' : IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      (e.map ((truncation 2).map (sliceOverProjection F)))) := by
    rw [← coneHomotopyMap_homMk (sliceOverProjection F) e]
    infer_instance
  have hj : IsIso (SSet.Truncated.HomotopyCategory₂.homMk
      (derivedConeLeg (initialValueCone hc F) (nerveVertex c))) := by
    have : IsIso (SSet.Truncated.HomotopyCategory₂.homMk
        (SSet.Truncated.Edge.id (X := (truncation 2).obj X) (F.app _ (nerveVertex c)))) := by
      rw [SSet.Truncated.HomotopyCategory₂.homMk_id]
      infer_instance
    exact coneEdge_isIso_of_edge_eq _ _ (initialValueCone_leg hc F)
  rw [← derivedConeLeg_homMk_comp e (nerveVertex c)]
  infer_instance

end SerrePositivity.BhattScholze.PerfectoidizationInterface
